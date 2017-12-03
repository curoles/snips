#!/bin/sh

SRCDIR=$1

make -C $SRCDIR clean

STAMP=`date +%F_%H`

tar -czvf COH-${STAMP}.tgz $SRCDIR
