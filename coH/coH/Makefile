#author    Igor Lesik 2012
#copyright Igor Lesik 2012

UNAME := $(shell whoami)
MBITS := $(shell getconf LONG_BIT)

SRC_DIR     ?= ./src
BUILD_DIR   ?= ../build
RELEASE_DIR := $(BUILD_DIR)/release
DEBUG_DIR   := $(BUILD_DIR)/debug
DOXY_DIR    := $(BUILD_DIR)/doxy

CC  ?= gcc
CXX ?= g++
AR  ?= ar

VALGRIND ?= `command -v valgrind`

SRCS := main.c debug.c cfg.c compiler.c
SRCS += String.c List.c trie.c
SRCS += SrcRead.c Scanner.c ast.c Parser.c
SRCS += CodeGen.c be_defClass.c

OBJS  := $(notdir $(SRCS:.c=.o))
rOBJS := $(addprefix $(RELEASE_DIR)/,$(OBJS))
dOBJS := $(addprefix $(DEBUG_DIR)/,$(OBJS))

rTARGET := $(RELEASE_DIR)/coh
dTARGET := $(DEBUG_DIR)/coh

#INCLUDES :=  -I.
#INCLUDES +=  -I

CFLAGS := -m$(MBITS) -D__STDC_FORMAT_MACROS $(INCLUDES)
CFLAGS += -Werror -Wall

dCFLAGS := $(CFLAGS) -O0 -g -DUNIT_TEST
rCFLAGS := $(CFLAGS) -O2 -DNDEBUG

define run-COH
@echo
@mkdir -p $(BUILD_DIR)/test
@$(VALGRIND) --leak-check=full $(dTARGET) ./std/Int.coh -o $(BUILD_DIR)/test
@time $(rTARGET)
@echo "cd $(BUILD_DIR)/test && cc test.c"
@echo
endef

all: $(BUILD_DIR) $(dTARGET) $(rTARGET)
	$(run-COH)
	@echo "== DONE! Master $(UNAME)! =="

# make build directory
$(BUILD_DIR):
	mkdir -p $(BUILD_DIR)
	mkdir -p $(DEBUG_DIR)
	mkdir -p $(RELEASE_DIR)
	mkdir -p $(DOXY_DIR)

# compile
$(DEBUG_DIR)/%.o: $(SRC_DIR)/%.c
	$(CC) -c $(dCFLAGS) -o $@ $<

$(RELEASE_DIR)/%.o: $(SRC_DIR)/%.c
	$(CC) -c $(rCFLAGS) -o $@ $<

# link
$(dTARGET): $(dOBJS)
	$(CC) $(dLFLAGS) $(dOBJS) -o $@

$(rTARGET): $(rOBJS)
	$(CC) $(rLFLAGS) $(rOBJS) -o $@

# generate file dependencies
DEPS = $(SRCS:.c=.d)
rDEPS := $(addprefix $(RELEASE_DIR)/,$(DEPS))
dDEPS := $(addprefix $(DEBUG_DIR)/,$(DEPS))

ifneq ($(MAKECMDGOALS),clean)
-include $(rDEPS)
-include $(dDEPS)
endif

$(DEBUG_DIR)/%.d: $(SRC_DIR)/%.c $(BUILD_DIR)
	@echo "make dependencies $@ for $<"
	@$(CC) $(dCFLAGS) -MF"$@" -MG -MM -MP -MT"$@" -MT"$(DEBUG_DIR)/$(notdir $(<:.c=.o))" "$<"

$(RELEASE_DIR)/%.d: $(SRC_DIR)/%.c $(BUILD_DIR)
	@echo "make dependencies $@ for $<"
	@$(CC) $(rCFLAGS) -MF"$@" -MG -MM -MP -MT"$@" -MT"$(RELEASE_DIR)/$(notdir $(<:.c=.o))" "$<"

# generate tags
tags:
	ctags -R --c++-kinds=+p --fields=+iaS --extra=+q .

cscope:
	rm -f cscope.*
	find ./ -name '*.[ch]' -print > cscope.files
	find ./ -name '*.[ch]pp' -print >> cscope.files
	cscope -b

# generate documentation
doc:
	mkdir -p $(DOXY_DIR)
	(cd $(SRC_DIR) && doxygen ./Doxyfile)

# show doc front page in html
seedoc:
	firefox $(BUILD_DIR)/doxy/html/index.html &

# clean all products
clean:
	rm -rf $(BUILD_DIR)
	rm -f tags
	rm -f cscope.*

.PHONY: all clean tags scope doc seedoc
