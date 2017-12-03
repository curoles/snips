# Halo front-end makefile.
#
# Copyright Igor Lesik 2011.
# License:   Distributed under the Boost Software License, Version 1.0.
#            (See http://www.boost.org/LICENSE_1_0.txt)
#


-include config.mk

CC  ?= gcc
CXX ?= g++
AR  ?= ar

UNAME := $(shell whoami)

SRC_DIR     := ./
BUILD_DIR   ?= ./../../build/compiler

USE_LLVM := yes

ifeq ($(USE_LLVM),yes)
LLVM_INCLUDE := $(LLVM_DIR)/include
LLVM_BIN     := $(LLVM_DIR)/bin
LLVM_CFLAGS  := $(shell $(LLVM_BIN)/llvm-config --cxxflags)
LLVM_CFLAGS  += -D__STDC_LIMIT_MACROS -D__STDC_CONSTANT_MACROS
LLVM_LDFLAGS := $(shell $(LLVM_BIN)/llvm-config --ldflags --libs core)
LLVM_LIBS    := $(shell $(LLVM_BIN)/llvm-config --libs core)
#core|backend|all
endif

SRCS := main.cpp debug.cpp cfg.cpp compiler.cpp srcread.cpp scan.cpp
SRCS += parser.cpp ast.cpp symtbl.cpp codegen.cpp
SRCS += trie.c
ifeq ($(USE_LLVM),yes)
SRCS += lvm/lcodegen.cpp
endif

OBJS := $(SRCS:.cpp=.o)
OBJS := $(OBJS:.c=.o)
OBJS := $(addprefix $(BUILD_DIR)/,$(OBJS))

TARGET := $(BUILD_DIR)/halo

INCLUDES :=  -I.
ifeq ($(USE_LLVM),yes)
INCLUDES += -I$(LLVM_INCLUDE)
endif

CFLAGS := -m64 -D__STDC_FORMAT_MACROS $(INCLUDES)
CFLAGS += -Wall -Werror
#CFLAGS += $(LLVM_CFLAGS)

LDFLAGS := -m64
LDFLAGS += $(LLVM_LDFLAGS)

ARFLAGS := -cvq

all: $(BUILD_DIR) $(TARGET)
	@echo "DONE!"

release: all
fast_release: all

# add gcc debug flags if !release build
ifeq ($(MAKECMDGOALS),release)
CFLAGS += -O3 -DNDEBUG
else
  ifeq ($(MAKECMDGOALS),fast_release)
  CFLAGS += -O3 -DNDEBUG -DHALO_FAST
  else
  CFLAGS += -g -O0
  endif
endif

# header dependencies
ifneq ($(MAKECMDGOALS),clean)
-include Depends.make
endif

# update dependencies
#Depends.make: SRCS := $(SRCS)
Depends.make: $(SRCS)
	touch Depends.make
	makedepend -Y -p$(BUILD_DIR)/ -f Depends.make $(SRCS) 2> /dev/null
	rm -f Depends.make.bak

# make build directory
$(BUILD_DIR):
	mkdir -p $(BUILD_DIR)
	mkdir -p $(BUILD_DIR)/lvm

# compile
$(BUILD_DIR)/%.o: $(SRC_DIR)/%.cpp
	$(CXX) -c $(CFLAGS) -o $@ $<

$(BUILD_DIR)/%.o: $(SRC_DIR)/%.c
	$(CXX) -c $(CFLAGS) -o $@ $<


$(BUILD_DIR)/lvm/lcodegen.o: CFLAGS := $(CFLAGS) $(LLVM_CFLAGS)

# link
$(TARGET): $(OBJS)
	$(CXX) $(LDFLAGS) -o $@ $^ $(LLVM_LIBS)

#$(AR) $(ARFLAGS) $(TARGET) $(OBJS)

# generate tags
tags:
	ctags -R --c++-kinds=+p --fields=+iaS --extra=+q .

# generate cscope DB
cscope:
	rm -f cscope.*
	find ./ -name '*.[ch]' -print > cscope.files
	find ./ -name '*.[ch]pp' -print >> cscope.files
	cscope -b

# generate documentation
doc:
	mkdir -p $(BUILD_DIR)/doxy
	doxygen Doxyfile

# show doc front page in html
seedoc:
	firefox build/doxy/html/index.html &

# clean all products
clean:
	rm -rf $(BUILD_DIR)
	rm -f Depends.make
	rm -f tags
	rm -f cscope.*

# show make targets
help:
	echo "Targets:"
	echo "  help         - print this help."
	echo "  all          - default debug build."
	echo "  release      - make release build."
	echo "  fast_release - make fast optimized release build."
	echo "  clean        - clean build directory and temporary files."
	echo "  tags         - generate ctags."
	echo "  cscope       - generate cscope DB."
	echo "  doc          - generate documentation with Doxygen."
	echo "  seedoc       - open doc index page in html browser."
	echo ""
	echo " Author: Igor Lesik, 2011."

.PHONY: all release fast_release clean tags cscope doc seedoc help

# END

# DO NOT DELETE
