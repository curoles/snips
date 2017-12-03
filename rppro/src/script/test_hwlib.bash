#!/bin/bash

#author: Igor Lesik 2013
#brief : Test individual RPPRO HW-LIB components

REL_PATH="${BASH_SOURCE[0]%/*}"


make -f ${REL_PATH}/../hwlib/Dff/test/sv/Makefile
make -f ${REL_PATH}/../hwlib/Rom/test/sv/Makefile
