RAC=${REL_PATH}/../../rac.rb
ODIR=${REL_PATH}/../../../build

CC=gcc

TEST=${REL_PATH}/test.ral

rm -f $ODIR/*.{o,h}
rm -f $ODIR/test

$RAC $TEST $ODIR > $ODIR/test.c
$CC $ODIR/test.c -o $ODIR/test

fail()
{
  echo "$REL_PATH: FAIL"
  exit 1
}

echo "Run $TEST"
$ODIR/test
[[ $? == 0 ]] || fail
