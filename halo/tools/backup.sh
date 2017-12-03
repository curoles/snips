#!/bin/sh
#
# Copyright Igor Lesik 2011.
# License:   Distributed under the Boost Software License, Version 1.0.
#            (See http://www.boost.org/LICENSE_1_0.txt)
#

if [ $# -ne 2 ]
then
  echo "Usage: `basename $0` source_dir output_dir"
  exit
fi

SOURCE_DIR=$1
OUTPUT_DIR=$2
ARCHIVE_NAME="`date +%F`-halo"
ARCHIVE_NAME_FULL=$OUTPUT_DIR/$ARCHIVE_NAME.tar.gz

echo "Source directory: $SOURCE_DIR"
echo "Output directory: $OUTPUT_DIR"
echo "Archive name    : $ARCHIVE_NAME"

echo ""
echo "Archiving..."
tar -czf $ARCHIVE_NAME_FULL $SOURCE_DIR

echo ""
echo "Listing of the contents of the archive $ARCHIVE_NAME_FULL:"
tar -tvf $ARCHIVE_NAME_FULL

echo ""
echo "Output directory:"
echo "`ls -lht $OUTPUT_DIR`"

echo ""
echo "Done!"
echo ""
