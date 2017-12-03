#!/bin/bash

# Run 'malachite' Ruby library unit tests.
# author: Igor Lesik 2013
#

THIS_SCRIPT_REL_PATH="${BASH_SOURCE[0]%/*}"

source $THIS_SCRIPT_REL_PATH/rppro.bash

MALACHITE_DIR=$THIS_SCRIPT_REL_PATH/../ruby/malachite

$RUBY -s $MALACHITE_DIR/ClassWithAttributes.rb -TEST

