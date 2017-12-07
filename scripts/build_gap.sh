#!/usr/bin/env bash
set -ex

# build GAP in a subdirectory
git clone --depth=2 https://github.com/gap-system/gap.git $GAPROOT
cd $GAPROOT
./autogen.sh
./configure
make -j4 V=1
make bootstrap-pkg-full

GAPROOT="$(cd .. && pwd)"

if [[ $ABI == 32 ]]
then
    CONFIGFLAGS="CFLAGS=-m32 LDFLAGS=-m32 LOPTS=-m32 CXXFLAGS=-m32"
fi

# build some packages...
cd pkg

cd io-*
./autogen.sh
./configure $CONFIGFLAGS
make -j4 V=1
cd ..

cd profiling-*
./autogen.sh
# HACK to workaround problems when building with clang
if [[ $CC = clang ]]
then
    export CXX=clang++
fi
./configure $CONFIGFLAGS
make -j4 V=1
cd ..
