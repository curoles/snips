#!/bin/sh

TEST_NAME=$1
INPUT_FILE=$2
BUILD_DIR=$3
TEST_DIR=$BUILD_DIR/test

echo Test name : $TEST_NAME
echo Input file: $INPUT_FILE
echo Build dir : $BUILD_DIR

HALOC=$BUILD_DIR/compiler/halo

IR_FILE=$TEST_DIR/$TEST_NAME.ir
BC_FILE=$TEST_DIR/$TEST_NAME.bc
ASM_FILE=$TEST_DIR/$TEST_NAME.s
OBJ_FILE=$TEST_DIR/$TEST_NAME.o

mkdir -p $TEST_DIR
rm $TEST_DIR/$TEST_NAME.*

echo
echo Compiling $INPUT_FILE ...
$HALOC $INPUT_FILE -o $IR_FILE

LLVM_DIR=/home/igor/tools/llvm-2.9-usr-local/bin/
LLAS=$LLVM_DIR/llvm-as
LLC=$LLVM_DIR/llc
LLVM_GCC_DIR=/home/igor/tools/llvm-gcc4.2-2.9-x86_64-linux/bin/
LLVM_GCC=$LLVM_GCC_DIR/llvm-gcc

$LLAS -f $IR_FILE -o $BC_FILE
$LLC $BC_FILE -o $ASM_FILE
$LLVM_GCC $ASM_FILE -o $OBJ_FILE

ls -lht  $TEST_DIR

echo Run $OBJ_FILE
./$OBJ_FILE
