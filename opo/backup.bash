#!/bin/sh

#
#@brief   Script to create source code archive
#@author  Igor Lesik 2012
#

if [ $# -lt 1 ]; then
  echo "Too few arguments"
  exit 1
fi

# directory to be archived
SRCDIR=$1

# archive name
ARNAME=OPO

HOST=`hostname`
STAMP=`date +%F_%H_$HOST`

tar -czvf ${ARNAME}-${STAMP}.tgz $SRCDIR
