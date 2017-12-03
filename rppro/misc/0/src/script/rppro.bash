#!/bin/bash

# RPPRO launching bash script.
# author: Igor Lesik 2013
#

##
# Print-out verbosity setting
#
if [ -z $RUBY ]
then
  QUIET=1
fi

##
# Debug print.
#
print()
{
  [ $QUIET -eq 1 ] || echo "$1"
}

##
# Function to print out message and exit.
#
# Usage example:
# some_command
# [ $? -eq 0 ] || failure "running some_command"
#
failure()
{
    echo "Failed at: $1"
    exit 1
}

##
# Load user's RPPRO configuration
#
USER_HOME_DIR=$HOME
USER_RPPRO_CFG=$USER_HOME_DIR/rppro.config

if [ ! -f $USER_RPPRO_CFG ]
then

  cat > $USER_RPPRO_CFG << EOF
#RUBY=/usr/bin/ruby1.9.1
#RDOC=/usr/bin/rdoc1.9.1
EOF

  failure echo "File $USER_RPPRO_CFG does not exists"
fi

source $USER_RPPRO_CFG


if [ -z $RUBY ]
then
  print "No RUBY env var"
  RUBY=`which ruby`
  print "path to Ruby:$RUBY"
  if [ -z $RUBY ]
  then
    echo "Ruby not installed"
    exit 1
  fi
fi

RUBYDIR=$(dirname $RUBY)

GEM=$RUBYDIR/gem

#$GEM list --local

get_ruby_version()
{
  $RUBY -e "major=RUBY_VERSION.to_i;minor=RUBY_VERSION.split('.')[1].to_i;ver=major*100+minor;exit ver"
  echo $?
}


RUBY_VER=$(get_ruby_version)
print "Ruby version: $RUBY_VER"

[ $RUBY_VER -gt 108 ] || failure "Ruby version '`$RUBY -v`' is older that 1.9"

#YOURS_TOP_DIR="$( cd "$(dirname "$0")" && pwd )"
#print "Yours top dir: $YOURS_TOP_DIR"
#
#
#MAIN="${YOURS_TOP_DIR}/-/r/u/b/y/main.rb"
#
#NAVIGATION="${YOURS_TOP_DIR}/-/r/u/b/y/navigation"
#
#YOURS_CMD_LINE="-s $MAIN $@ -YOURS_TOP_DIR=$YOURS_TOP_DIR -NAVIGATION=$NAVIGATION"
#
#if [ "$MAKE_DOC" != "" ]
#then
#  RDOC_DIR=${YOURS_TOP_DIR}/../rdoc
#  rm -rf $RDOC_DIR
#  $RDOC --main $MAIN --op $RDOC_DIR --all
#  exit 0
#fi
#
#if [ "$TEST_YOURS" != "" ]
#then
#  $RUBY $YOURS_CMD_LINE -TEST
#else
#  $RUBY $YOURS_CMD_LINE
#fi

