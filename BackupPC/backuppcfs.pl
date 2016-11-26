#!/usr/bin/perl

# backuppcfs - a fuse module to access backuppc backups through the filesystem.
# Copyright (C) 2009  Pieter Wuille
# Based on the backuppc-fuse script by Stephen Day
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.

# Changelog:
# - 2009 Nov 10: default_permissions on by default
# - 2009 Jun 10: LRU cache to limit number of cached nodes
# - 2009 Jun 09: Correction of absolute symlinks
# - 2009 Jun 05: Errors propagate forced re-reads upwards
# - 2009 Jun 05: Support for type!=mode, hardlinks, empty files
# - 2009 Jun 03: Full directory merging (for share-directories)
# - 2009 Jun 02: Initial version

# Changes w.r.t. Stephen Day's version:
# - cached tree - huge speedup
# - support for character/blockdevices
# - correct linkcounts for directories
# - support for /'s in sharenames
# - daemonization
# - stateful open()'s to prevent seeking for every read
# - correct merged view for incremental backups
# - latest/oldest link in hosts to latest/oldest archive
# - getopt for somewhat more configurability
# - support for empty files
# - support for xfermethods that don't set filetype bits in mode, like tar
# - support for hardlinks (linkcount=1, however)

# TODO:
# - testing!
# - error output/logging
# - escaping of dangerous characters in host/sharenames
# - fsstats
# - mtime of root/hosts/links
# - forced uid/perms/umask of virtual dirs/all dirs
# - uid mapping
# - common getattr generation - a lot seems shared
# - mtime for virtual dirs (eg. most recent backup)
# - some way of finding the last/first backup before/after a given date/time?

use strict;

use Fuse;
use Fcntl ':mode';
use POSIX qw/EROFS EOPNOTSUPP ENOENT EINVAL setsid strftime/;
use Getopt::Long qw(:config permute bundling);
require Carp;


use lib "/usr/share/backuppc/lib";
use lib "/usr/share/BackupPC/lib";
use BackupPC::Lib;
use BackupPC::View;
use BackupPC::Attrib qw(:all);

my $TTL_ROOT    = 80000; # don't expect new hosts within a day
my $TTL_HOST    = 40000; # don't expect new archives within half a day
my $TTL_ARCHIVE = 1000000; # +- infinite timeout for archives/shares
my $TTL_SHARE   = 1000000; # as as long as they exist, their content
my $TTL_REST    = 1000000; # does not change

my $BLKSIZE     = 512;     # reasonable number - is it used for anything?
my $DEFDEV      = 0;
my $DEFINODE    = 1;
my $DEFUID      = $<;            # your uid
my ($DEFGID)    = split(/ /,$(); # your gid
my $DEFPERM     = 0755;          # u=rwx,g=rx,o=rx (for directories)
my $CORLINKS    = 0;        # modify absolute symlinks to point to the archive root
my $MOUNTPOINT  = undef;
my $MAXCACHE    = 2048;

#my $CONF_REALINODES = 1;

#################################
########### LRU lib #############
#################################

# an LRU (least recently used) datastructure:
# a circular double-linked list, with one
# marker node (which initially refers to itself)
# the data of the marker node is a hash reference
# that maps data elements to the lru nodes containing them
# each node is [$prevRef,$data,$nextRef], while the
# marker node is [$lastRef,$hash,$firstRef]

# create a new lru data structure
sub lru_create {
  my $x=[undef,{},undef];
  $x->[0]=$x;
  $x->[2]=$x;
  return $x;
}

# delete an entry from an lru
sub lru_delete {
  my ($lru,$data) = @_;
  my $x = $lru->[1];
  if (exists $x->{$data}) {
    my $n = $x->{$data};
    my $prev = $n->[0];
    my $next = $n->[2];
    $prev->[2] = $next;
    $next->[0] = $prev;
    @{$n} = ();
    delete $x->{$data};
  }
}

# move an entry to the end of the structure, creating it if necessary
sub lru_access {
  my ($lru,$data) = @_;
  my $x = $lru->[1];
  my $n;
  my $last;
  if (defined $x->{$data}) {
    $n = $x->{$data}; # find existing node
    my $prev = $n->[0]; # find its predecessor/successor
    my $next = $n->[2];
    $prev->[2] = $next; # make them point to eachother
    $next->[0] = $prev;
    $last = $lru->[0];
    $n->[0] = $last; # make the reused node know its new predecessor/successor
    $n->[2] = $lru;
  } else {
    $last = $lru->[0];
    $n = [$last,$data,$lru]; # create new node
    $x->{$data} = $n; # add it to the hashtable
  }
  $last->[2] = $n; # insert the entry itself
  $lru->[0] = $n;
}

# destroy a complete lru structure
sub lru_destroy {
  my ($lru) = @_;
  my $x = $lru;
  while (defined $x->[2]) {
    my $nx = $x->[2];
    undef @{$x};
    $x = $nx;
  }
}

# retrieve the element least recently lru_access'ed
sub lru_lru {
  my ($lru) = @_;
  my $x = $lru->[2];
  return undef if ($x == $lru);
  return $x->[1];
}

# calculate the size of the lru
sub lru_size {
  my ($lru) = @_;
  return (0+(keys %{$lru->[1]}));
}

#################################
########## cache lib ############
#################################

# a cached array is represented as an array reference containing:
# - a function reference to call when the data has expired
# - a scalar to pass to the function
# - a ttl value (in seconds)
# - an expiration time (seconds sinds epoch when current value expires, -1 if certainly/already expired)
# - ref to the cached array

# if a cache has subentries, these must be the values of a hash, referenced by the first value returned

my $cachelru = lru_create();
my %cachefn;

# create a cached value (function ref,data,ttl)
sub cache_create {
  my ($fn,$data,$ttl) = @_;
  my @ret = ($fn,$data,$ttl,-1,undef);
  return \@ret;
}

sub cache_evict {
  my ($cache) = @_;
  if (defined $cache->[2] && defined $cache->[4]) {
    lru_delete($cachelru,$cache);
  }
  if (defined $cache->[4]) {
    my $d = $cache->[4];
    if (defined $d->[0]) {
      foreach my $x (values %{$d->[0]}) {
        cache_evict($x);
      }
    }
  }
}

sub cache_purge {
  while (lru_size($cachelru) > $MAXCACHE) {
    my $old = lru_lru($cachelru);
    cache_evict($old);
    $old->[3] = -1;
    $old->[4] = undef;
  }
}

# read data from cache (refreshing it if necessary)
sub cache_read {
  my ($cache,$force) = @_;
  cache_purge;
  my $nt = time;
  if (defined($cache->[2]) && (defined($force) || ($cache->[3] < $nt))) {
    cache_evict($cache);
    my @ret;
    @ret = $cachefn{$cache->[0]}->($cache->[1]);
    $cache->[4] = \@ret;
    $cache->[3] = $nt+$cache->[2];
  }
  lru_access($cachelru,$cache) if (defined($cache->[2]));
  return (@{$cache->[4]});
}

# create a cached object that returns a constant array
sub cache_const {
  my @val = @_;
  my @ret = (undef,undef,undef,undef,\@val);
  return \@ret;
}

#################################
######## tree functions #########
#################################

# the filesystem is internally represented by a (cached, see above) tree
# each node is a cached array containing these elements:
# - ref to hash containing [filename -> cached array] mappings
# - attributes (corresponding to getinfo)
# - backuppc attributes object
# - actual data (currently: link data for symlinks)

# reuse the same backuppc Lib object
my $bpc;
sub bpc {
  if (!defined $bpc) {
    $bpc = BackupPC::Lib->new(undef,undef,"",1);
  }
  return $bpc;
}

# a cache refresher that builds on top of another (directory) node, and adds some static subentries to it
sub fs_dirmerge {
  my ($data) = @_;
  my ($type,$sdata,$ndir,$ent) = @{$data}; # nodetype name, data for node, number of added subentries that are dirs, hashref of subentries
  my ($sub,$attr,$a) = $cachefn{$type}->($sdata);
  return undef if (!defined $attr);
  if (S_ISDIR($attr->[2])) {
    my %nsub = %{$sub};
    my @nattr = @{$attr};
    foreach my $k (keys %{$ent}) {
      if (exists $nsub{$k}) { # a collision occurred
        my ($s1sub,$s1attr,$s1a) = cache_read($ent->{$k}); # check whether entry to add is a directory
        if (S_ISDIR($s1attr->[2])) {
          my ($s2sub,$s2attr,$s2a) = cache_read($nsub{$k}); # check whether entry in original dir is a directory
          if (S_ISDIR($s2attr->[2])) { # if so, substitute it with a new merge node
            $nsub{$k} = cache_create('dirmerge',[$nsub{$k}->[0],$nsub{$k}->[1],$s1attr->[3]-2,$s1sub],$nsub{$k}->[2]);
            next;
          }
        }
        if (!exists $nsub{$k.'_'}) { # try adding '_' otherwise
          $nsub{$k.'_'} = $ent->{$k};
          next;
        }
        my $i=1;
        $i++ while (exists $nsub{$k.'_'.$i}); # try adding subsequent '_<num>' otherwise
        $nsub{$k.'_'.$i} = $ent->{$k};
      } else {
        $nsub{$k} = $ent->{$k};
      }
    }
    $nattr[3] += $ndir;
    return (\%nsub,\@nattr,$a);
  } else {
    Carp::croak "Unable to add subentries to a non-directory"
  }
}

# the root cache refresher, no arguments
sub fs_root {
  my $bpc=bpc();
  return undef if (!defined $bpc);
  my $hosts = $bpc->HostInfoRead();
  return undef if (!defined $hosts);
  my %hlist = map { ($_,cache_create('host',$_,$TTL_HOST)) } (keys %{$hosts});
  return (\%hlist,[$DEFDEV,$DEFINODE,S_IFDIR | $DEFPERM,2 + keys %hlist,$DEFUID,$DEFGID,0,1024,0,0,0,$BLKSIZE,2],undef);
}

sub fmtTime {
  my ($ut) = @_;
  return (strftime "%Y-%m-%d %H:%M:%S", localtime $ut);
}

# the host cache refresher, arguments (host)
sub fs_host {
  my ($host) = @_;
  my @archives = (bpc()->BackupInfoRead($host));
  return undef if ($#archives<0);
  my $lnum = undef;
  my $onum = undef;
  my $view = BackupPC::View->new(bpc(), $host, \@archives);
  return undef if (!defined $view);
  my %alist = map { 
    $lnum=$_->{num} if (!defined($lnum) || $_->{num}>$lnum); 
    $onum=$_->{num} if (!defined($onum) || $_->{num}<$onum); 
    (
      $_->{num},cache_create('archive',[$_,$view],$TTL_ARCHIVE),
      fmtTime($_->{startTime}),cache_const(undef,[$DEFDEV,$DEFINODE,S_IFLNK | $DEFPERM,1,$DEFUID,$DEFGID,0,length($_->{num}),0,0,0,$BLKSIZE,0],undef,$_->{num})
    )
  } (@archives);
  $alist{latest} = cache_const(undef,[$DEFDEV,$DEFINODE,S_IFLNK | $DEFPERM,1,$DEFUID,$DEFGID,0,length($lnum),0,0,0,$BLKSIZE,0],undef,"$lnum") if (defined($lnum));
  $alist{oldest} = cache_const(undef,[$DEFDEV,$DEFINODE,S_IFLNK | $DEFPERM,1,$DEFUID,$DEFGID,0,length($onum),0,0,0,$BLKSIZE,0],undef,"$onum") if (defined($onum));
  return (\%alist,[$DEFDEV,$DEFINODE,S_IFDIR | $DEFPERM,2 + @archives,$DEFUID,$DEFGID,0,1024,0,0,0,$BLKSIZE,2],undef);
}

# recursive helper function to build a tree containing all shares
sub buildtree {
  my ($node,$view,$archive) = @_;
  my %sub; # hash for all subdirectories
  foreach my $se (keys %{$node}) {
    $sub{$se} = buildtree($node->{$se},$view,$archive) if ($se ne '');
  }
  if (exists $node->{''}) {
    my $se = [$view,$archive,$node->{''},undef,''];
    return cache_create('dirmerge',['share',$se,0+(keys %sub),\%sub],$TTL_SHARE) if ((keys %sub)>0); # both a share and virtual sharename-dirs
    return cache_create('share',$se,$TTL_SHARE); # only a real share
  } else { # only a virtual sharename dir
    my $archivetime = $archive->{startTime};
    return cache_const(\%sub,[$DEFDEV,$DEFINODE,S_IFDIR | $DEFPERM,2 + keys %sub,$DEFUID,$DEFGID,0,1024,$archivetime,$archivetime,$archivetime,$BLKSIZE,2],undef);
  }
}

# the archive cache refresher, arguments [archiveref,view]
sub fs_archive {
  my ($data) = @_;
  my ($archive,$view) = @{$data};
  my $archivenum = $archive->{num};
  my @shares = $view->shareList($archivenum);
  return undef if ($#shares<0);
  my %tree; # abstract tree - each node can have some name->subnode mappings for subdirs, and/or a '' entry referring to a share
  foreach my $share (@shares) { # loop over all shares
    my @path = grep { $_ ne '' && $_ ne '.' && $_ ne '..' } (split(/[\\\/]+/,$share)); # split them in pieces (both / and \ seen as separators)
    my $node = \%tree; # start at the root - node is a hashref to the current treenode
    while ($#path >= 0) { # while there are path components left
      my $ent = shift @path; # get a component
      $node->{$ent}={} if (!exists $node->{$ent}); # create empty subnode if it doesn't exist yet
      $node = $node->{$ent}; # travel down
    }
    $node->{''} = $share; # finally make the reached leaf node point to the share (full, original share name)
  }
  return cache_read(buildtree(\%tree,$view,$archive)); # now call helper funtion to turn it into a tree of cached arrays and evaluate it
}

# mapping from backuppc file types to stat() file type modes
my %iftype = (
  BPC_FTYPE_FILE,     S_IFREG,
  BPC_FTYPE_HARDLINK, S_IFLNK,
  BPC_FTYPE_SYMLINK,  S_IFLNK,
  BPC_FTYPE_CHARDEV,  S_IFCHR,
  BPC_FTYPE_DIR,      S_IFDIR,
  BPC_FTYPE_FIFO,     S_IFIFO,
  BPC_FTYPE_SOCKET,   S_IFSOCK,
  BPC_FTYPE_UNKNOWN,  0,
  BPC_FTYPE_DELETED,  0
);

# the share/backupdata cache refresher, arguments [view,archive,share,fileattr,path]
sub fs_share {
  my ($data) = @_;
  my ($view,$archive,$share,$a,$path) = @{$data};
  my $archivenum = $archive->{num};
  my $ino = $DEFINODE;
  my $dev = $DEFDEV;
#  if (defined($a) && $CONF_REALINODES) {
#    ($dev,$ino) = stat($a->{fullPath});
#  }
  if (!defined($a) || $a->{type}==BPC_FTYPE_DIR) { # directory (root dir which has no $a, or subdir which does)
    my $nattr = $view->dirAttrib($archivenum,$share,$path); # get attributes/list of directory entries
    return undef if (!defined $nattr);
    my $sdirs = 0; # number of subdirectories
    my %sub = map {
      my $key=$_;
      my $val = $nattr->{$key};
      $sdirs++ if ($val->{type}==BPC_FTYPE_DIR); # count subdirs
      ($key,cache_create('share',[$view,$archive,$share,$val,$path.'/'.$key],$TTL_REST))
    } (keys %{$nattr});
    if (!defined($a)) { # root of share
      my $archivetime = $archive->{startTime};
      return (\%sub,[$dev,$ino,S_IFDIR | $DEFPERM,2 + $sdirs,$DEFUID,$DEFGID,0,1024,$archivetime,$archivetime,$archivetime,$BLKSIZE,2],undef);
    } else { # subdir in share
      my $mtime = $a->{mtime};
      my $size = ( $a->{sizeDiv4GB} * 1024 * 1024 * 1024 * 4 ) + $a->{sizeMod4GB};
      my $blocks = int ( $size / 512 );
      if ($size==0) { # some xfermethods don't store a meaningful size for directories
        $size = 1024;
        $blocks = 2;
      }
      return (\%sub,[$dev,$ino,S_IFDIR | ($a->{mode} & ~S_IFMT),2 + $sdirs,$a->{uid},$a->{gid},0,$size,$mtime,$mtime,$mtime,$BLKSIZE,$blocks],$a);
    }
  } else { # non-directory
    my $mtime = $a->{mtime};
    my $size = ( $a->{sizeDiv4GB} * 1024 * 1024 * 1024 * 4 ) + $a->{sizeMod4GB};
    my $blocks = int ( $size / 512 );
    my $rdev = 0;
    my $fdata;
    my $mode = ($a->{mode} & (~S_IFMT)) | $iftype{$a->{type}};
    if (S_ISLNK($mode) || S_ISCHR($mode) || S_ISBLK($mode)) { # link, character or block device: read real backup data
      my $f = BackupPC::FileZIO->open($a->{fullPath}, 0, $a->{compress});
      return undef if (!defined $f);
      $f->read(\$fdata,65536);
      $f->close;
    }
    if ((S_ISCHR($mode) || S_ISBLK($mode)) && $fdata =~ /(\d+),(\d+)/) {
      $rdev = $1*256 + $2;
    }
    if ($a->{type} == BPC_FTYPE_HARDLINK) {
      my $sa = $view->fileAttrib($archivenum,$share,'/'.$fdata);
      return undef if (!defined $sa);
      return fs_share([$view,$archive,$share,$sa,$fdata]);
    }
    if ($a->{type} == BPC_FTYPE_SYMLINK) {
      if ($CORLINKS && ((substr $fdata,0,1) eq '/')) {
        $fdata = $MOUNTPOINT . '/' . $view->{host} . '/' . $archivenum . '/' . $fdata;
      }
    }
    return (undef,[$dev,$ino,$mode,1,$a->{uid},$a->{gid},$rdev,$size,$mtime,$mtime,$mtime,$BLKSIZE,$blocks],$a,$fdata);
  }
}

my $root = cache_create('root',undef,$TTL_ROOT);

%cachefn = (
  root => \&fs_root,
  host => \&fs_host,
  archive => \&fs_archive,
  share => \&fs_share,
  dirmerge => \&fs_dirmerge,
);

# lookup a node in the tree
sub get_data {
  my ($path) = @_;
  my @path = grep { $_ ne '' && $_ ne '.' && $_ ne '..' } (split(/\/+/,$path));
  my $done="";
  my $node = $root;
  foreach my $ent (@path) {
    my ($sub,$attr) = (cache_read($node));
    if (!defined $attr) { # entry itself doesn't seem te exist - cache tree is wrong
      prop_failure($done);
      return undef;
    }
    ($sub)=(cache_read($node,1)) if (!defined $sub || !defined $sub->{$ent}); # requested subnode does not seem te exist - force re-read
    return undef if (!defined $sub || !defined $sub->{$ent}); # it really doesn't exist
    $done .= '/'.$ent;
    $node = $sub->{$ent};
  }
  return cache_read($node);
}

# called when a particular path doesn't seem to exist anymore - forces re-evaluations until
# it finds what caused the failure
sub prop_failure {
  my ($path) = @_;
  my @path = grep { $_ ne '' && $_ ne '.' && $_ ne '..' } (split(/\/+/,$path)); # path components
  my @node = ($root); # subsequent nodes in the (currently cached) tree
  my @ent = (); # entries we'd like to exist
  while (@path) {
    my $ent = shift @path;
    push @ent,$ent;
    my ($sub,$attr) = (cache_read($node[$#node]));
    last if (!defined $attr);
    return if (!defined $sub);
    return if (!exists $sub->{$ent});
    last if (!@path);
    push @node,$sub->{$ent};
  }
  while (@node) {
    my $node = pop @node;
    my $ent = pop @ent;
    my ($sub,$attr) = (cache_read($node,1));
    last if (!defined $ent || (defined $attr && (!defined $sub || !exists $sub->{$ent})));
  }
}

#################################
######## Fuse functions #########
#################################

sub bpc_getattr {
  my ($path) = @_;
  my ($sub,$attr) = get_data($path);
  return -ENOENT() if (!defined $attr);
  return (@{$attr});
}

sub bpc_readlink {
  my ($path) = @_;
  my ($sub,$attr,$a,$fd) = get_data($path);
  return -ENOENT() if (!defined $attr);
  return -EINVAL() if (!defined $fd);
  return $fd;
}

sub bpc_getdir {
  my ($path) = @_;
  my ($sub) = get_data($path);
  return -ENOENT() if (!defined $sub);
  my @list = keys %{$sub};
  return ( '.', '..', @list, 0 );
}

sub bpc_rwop {
  return -EROFS();
}

sub bpc_unsupp {
  return -EOPNOTSUPP();
}

my %files; # pathname -> [(zio,pos)] # zio==undef means file is empty

sub bpc_open {
  my ($path,$mode) = @_;
  my ($sub,$attr,$a) = get_data($path);
  return -ENOENT() if (!defined $attr);
  my $zio;
  if ($attr->[7]!=0) { # non-empty file
    $zio = BackupPC::FileZIO->open($a->{fullPath}, 0, $a->{compress}); # create zio object
    if (!defined $zio) {
      my $err = 0-$!;
      prop_failure($path);
      return $err;
    }
  }
  push @{$files{$path}},[$zio,0]; # add the zio (which now has position 0) to the list of zio's for the requested file
  return 0;
}

sub bpc_release {
  my ($path,$mode) = @_;
  my $lastpos=-1;
  my $lasti=undef;
  my $lst = $files{$path};
  # find zio with highest pos
  foreach my $i (0..$#{$lst}) {
    my $ent = $lst->[$i];
    my ($zio,$pos) = @{$ent};
    if ($pos>$lastpos) {
      $lastpos = $pos;
      $lasti = $i;
    }
  }
  if (!defined $lasti) { # fail miserably when nothing found - this means a fuse 'release' call happened without corresponding 'open' call
    Carp::croak "Closing unopened file '$path'";
  }
  my ($zio) = @{$lst->[$lasti]}; # retrieve that 'best' zio
  $zio->close() if (defined $zio); # close it
  if ($#{$lst}==0) { # remove it from the hash
    delete $files{$path};
  } else {
    splice @{$files{$path}},$lasti,1;
  }
}

sub bpc_read {
  my ($path,$size,$offset) = @_;
  my $bestpos=-1;
  my $besti=undef;
  my $lst = $files{$path};
  # find zio with highest pos - if possible highest pos <= offset, otherwise highest pos whatsoever
  foreach my $i (0..$#{$lst}) {
    my $ent = $lst->[$i];
    my ($zio,$pos) = @{$ent};
    if (($pos<=$offset && ($pos>$bestpos || $bestpos>$offset)) || ($pos>$offset && $pos>$bestpos && ($bestpos>$offset || $bestpos<0))) {
      $bestpos = $pos;
      $besti = $i;
    }
  }
  if (!defined $besti) { # fail miserable when nothing was found - it means fuse requested a read from an unopened file
    Carp::croak "Reading from unopened file '$path'";
  }
  my ($zio,$pos) = @{$lst->[$besti]}; # retrieve zio object and its file position
  return '' if (!defined $zio);
  if ($pos>$offset) {
    $zio->rewind; # rewind the zio object if it already passed the requested start position for the read
    $pos=0;
  }
  my $data;
  while ($pos<$offset) { # as long a there is unrequested data left, seek
    my $do = $offset-$pos;
    $do=65536 if ($do>65536);
    my $ret = $zio->read(\$data,$do);
    if ($ret<=0) { # upon eof, return nothing; upon error, return failure
      $lst->[$besti]->[1]=$pos;
      if ($ret<0) {
        my $err = 0 - $!;
        prop_failure($path);
        return $ret;
      }
      return '';
    }
    $pos += $ret;
  }
  my $ret = $zio->read(\$data,$size); # do the actual read request
  if ($ret<=0) { # upon eof, return nothing, upon error, return failure
    $lst->[$besti]->[1]=$pos;
    if ($ret<0) {
      my $err = 0 - $!;
      prop_failure($path);
      return $ret;
    }
    return '';
  }
  $pos += $ret; # update position
  $lst->[$besti]->[1]=$pos; # update position in hash
  return $data; # return data
}

sub bpc_statfs {
  return 0;
}

sub bpc_flush {
  return 0;
}

sub bpc_fsync {
  return 0;
}

#################################
############# Main ##############
#################################

my $showhelp = 0;
my $foreground = 0;
my %fuseopts = ('default_permissions');

my $ok = GetOptions(
  'foreground|f!' => \$foreground,
  'uid|u=i' => sub { $DEFUID = $_[1]; die "uid out of range: $_[1]" if ($DEFUID<0 || $DEFUID>65535) },
  'gid|g=i' => sub { $DEFGID = $_[1]; die "gid out of range: $_[1]" if ($DEFGID<0 || $DEFGID>65535) },
  'user|U=s' => sub { $DEFUID = getpwnam($_[1]); die "unknown user '$_[1]'" if (!defined $DEFUID) },
  'group|G=s' => sub { $DEFGID = getgrnam($_[1]); die "unknown group '$_[1]'" if (!defined $DEFGID) },
  'mode|m=o' => sub { $DEFPERM = $_[1]; die "mode out of range: $_[1]" if ($DEFPERM<0 || $DEFPERM>32767) },
  'cache|c=i' => sub { $MAXCACHE = $_[1]; die "cache out of range: $_[1]" if ($MAXCACHE<32 || $MAXCACHE>1048576) },
  'correct-links|l!' => \$CORLINKS,
  'help|h|?' => \$showhelp,
  'o=s' => sub { foreach my $opt (split /,+/,$_[1]) { if (substr($opt,0,3) eq 'no_') { delete $fuseopts{lc $opt} } else { $fuseopts{lc $opt}=1; } } },
);
if ($ok && !$showhelp) {
  if ($#ARGV>=0) {
    $MOUNTPOINT = shift(@ARGV) if ($#ARGV>=0);
  }
  $ok = 0 if (!defined $MOUNTPOINT);
}
if ($ok && !$showhelp) {
  die "mountpoint '$MOUNTPOINT' if not valid" if (! -d $MOUNTPOINT);
}

if (!$ok || $showhelp) {
  print "Usage: $0 [options] mountpoint\n";
  print "\n";
  print "Options:\n";
  print "  -u,--uid UID         Use UID as owner of the mounted filesystem\n";
  print "  -U,--user USER       Use USER as owner of the mounted filesystem\n";
  print "  -g,--gid GID         Use GID as owner of the mounted filesystem\n";
  print "  -G,--group GROUP     Use GROUP as owner of the mounted filesystem\n";
  print "  -m,--mode MODE       Use MODE as permissions of the filesystem\n";
  print "  -h,--help            Show this help text\n";
  print "  -f,--foreground      Do not daemonize\n";
  print "  -l,--correct-links   Correct absolute symlinks - mountpoint must be absolute\n";
  print "  -c,--cache SIZE      Keep directory cache smaller than SIZE nodes\n";
  print "  -o OPT1[,OPT2[,...]] Fuse options\n";
  print "\n";
  print "FUSE options (may or may not work, depending on fuse version):\n";
  print "  -o allow_other            allow access to other users\n";
  print "  -o nonempty               allow mounts over non-empty file/dir\n";
  print "  -o no_default_permissions disable permission checking by kernel\n";
  print "  -o fsname=NAME            set filesystem name\n";
  print "\n";
  print "By default you/your primary group are owners of the filesystem\n";
  print "directories, using mode 0755 (owner rwx, others rx).\n";
  print "Use 'fusermount -u mountpoint' to unmount.\n";
  print "By daemonizing (default), no errors will be shown.\n";
  exit (!$ok);
}

# daemonize
sub daemonize {
  umask 0;
  open STDIN,  '</dev/null' or die "Can't read /dev/null: $!";
  open STDOUT, '>/dev/null' or die "Can't write to /dev/null: $!";
  open STDERR, '>/dev/null' or die "Can't write to /dev/null: $!";
  defined(my $pid = fork)   or die "Can't fork: $!";
  exit if $pid;
  setsid                    or die "Can't start a new session: $!";
}

daemonize if (!$foreground);

# run fuse
Fuse::main(
  mountopts  => join(',',keys %fuseopts), 
  mountpoint => $MOUNTPOINT, 
  threaded   => 0,
  debug      => 0,

  # supported operations
  open=>        \&bpc_open,
  release=>     \&bpc_release,
  getattr=>     \&bpc_getattr, 
  readlink=>    \&bpc_readlink, 
  getdir=>      \&bpc_getdir,
  read=>        \&bpc_read,
  flush=>       \&bpc_flush,
  statfs=>	\&bpc_statfs,

  # not meaningful for read-only view
  write=>       \&bpc_rwop,
  mknod=>       \&bpc_rwop, 
  mkdir=>       \&bpc_rwop, 
  unlink=>      \&bpc_rwop,
  rmdir=>       \&bpc_rwop, 
  symlink=>     \&bpc_rwop,
  rename=>      \&bpc_rwop,
  link=>        \&bpc_rwop,
  chmod=>       \&bpc_rwop,
  chown=>       \&bpc_rwop,
  truncate=>    \&bpc_rwop,
  utime=>       \&bpc_rwop,
  fsync=>	\&bpc_fsync,

  # not supported
  setxattr=>    \&bpc_unsupp,
  getxattr=>    \&bpc_unsupp,
  listxattr=>   \&bpc_unsupp,
  removexattr=> \&bpc_unsupp

);

lru_destroy($cachelru);
