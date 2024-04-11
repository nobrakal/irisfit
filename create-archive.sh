#!/bin/bash
set -euo pipefail
IFS=$'\n\t'

if command -v gnutar >/dev/null ; then
  # On MacOS, run "sudo port install gnutar" to obtain gnutar.
  TAR=gnutar
else
  TAR=tar
fi

ARCHIVE=irisfit

rm -rf $ARCHIVE $ARCHIVE.tar.gz

mkdir $ARCHIVE

make clean

cp -r \
   AUTHORS \
   Makefile \
   irisfit.opam \
   setup.sh \
   LICENSE \
   README.md \
   dune-project \
   metrics.sh \
   src \
   $ARCHIVE

$TAR cvfz $ARCHIVE.tar.gz \
   --exclude-ignore-recursive=.gitignore \
   --exclude-ignore-recursive=.lia.cache \
   --owner=0 --group=0 \
   $ARCHIVE

rm -rf $ARCHIVE
