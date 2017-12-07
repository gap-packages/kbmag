#!/usr/bin/env bash
set -ex

# ensure coverage is turned on
export CFLAGS="$CFLAGS -fprofile-arcs -ftest-coverage"
export LDFLAGS="$LDFLAGS -fprofile-arcs"

if [[ $ABI = 32 ]]
then
    export CFLAGS="$CFLAGS -m32"
    export LDFLAGS="$LDFLAGS -m32"
fi

# build this package
./configure $GAPROOT
make

# ... and link it into GAP pkg dir
ls
ls $GAPROOT
ls $GAPROOT/pkg
rm -r $GAPROOT/pkg/kbmag-*
ln -s $PWD $GAPROOT/pkg/
