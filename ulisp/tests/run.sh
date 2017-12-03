#!/bin/bash

REL_PATH=$(dirname ${BASH_SOURCE[0]})

ROOT_BUILD_DIR=${REL_PATH}/../../build

VALGRIND=valgrind

die()
{
    echo "Error: $1"
    exit 1
}

make -f $REL_PATH/../Makefile BUILD_DIR=$ROOT_BUILD_DIR/ulisp SRC_DIR=$REL_PATH/..
[ $? == 0 ] || die "making uLisp"

for dir in ${REL_PATH}/*/
do
    TEST_DIR=${dir%*/}
    TEST_NAME=${TEST_DIR##*/}
    BUILD_DIR=${ROOT_BUILD_DIR}/tests/${TEST_NAME}
    mkdir -p $BUILD_DIR
    make -f ${REL_PATH}/Makefile TEST_DIR=$TEST_DIR BUILD_DIR=$BUILD_DIR
    [ $? == 0 ] || die "making test $TEST_NAME"
    $VALGRIND $BUILD_DIR/test
    [ $? == 0 ] || die "running test $TEST_NAME"
done
