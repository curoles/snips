#author    Igor Lesik 2013
#copyright Igor Lesik 2013

CC  ?= gcc
CXX ?= g++
AR  ?= ar

VALGRIND ?= `command -v valgrind`

SRC_DIR     ?= ./
BUILD_DIR   ?= ../build/ulisp
DOXY_DIR    := $(BUILD_DIR)/doxy

SRCS_LISP := cell.cpp primitives.cpp eval.cpp
SRCS := $(SRCS_LISP) main.cpp

OBJS  := $(notdir $(SRCS:.cpp=.o))
OBJS  := $(addprefix $(BUILD_DIR)/,$(OBJS))

LIB_OBJS  := $(notdir $(SRCS_LISP:.cpp=.o))
LIB_OBJS  := $(addprefix $(BUILD_DIR)/,$(LIB_OBJS))

TARGET := $(BUILD_DIR)/lisp
LISPLIB := $(BUILD_DIR)/libulisp.a

UNAME := $(shell whoami)
MBITS := $(shell getconf LONG_BIT)

INCLUDES :=  -I.

CFLAGS := -m$(MBITS) -D__STDC_FORMAT_MACROS $(INCLUDES)
CFLAGS += -Werror -Wall

CFLAGS += $(CFLAGS) -O0 -g -DUNIT_TEST
#CFLAGS := $(CFLAGS) -O2 -DNDEBUG


all: $(BUILD_DIR) $(LISPLIB) $(TARGET)
	@echo "== DONE! =="

# make build directory
$(BUILD_DIR):
	mkdir -p $(BUILD_DIR)

# compile
$(BUILD_DIR)/%.o: $(SRC_DIR)/%.cpp
	$(CXX) -c $(CFLAGS) -o $@ $<

# link
$(TARGET): $(LISPLIB) $(BUILD_DIR)/main.o
	$(CXX) $(LFLAGS) $(BUILD_DIR)/main.o -Wl,--library=:$(LISPLIB) -o $@

$(LISPLIB): $(LIB_OBJS)
	$(AR) -r $(LISPLIB) $(LIB_OBJS)

# generate file dependencies
DEPS = $(SRCS:.cpp=.d)
DEPS := $(addprefix $(BUILD_DIR)/,$(DEPS))

ifneq ($(MAKECMDGOALS),clean)
-include $(DEPS)
endif

$(BUILD_DIR)/%.d: $(SRC_DIR)/%.cpp $(BUILD_DIR)
	@echo "make dependencies $@ for $<"
	@$(CXX) $(CFLAGS) -MF"$@" -MG -MM -MP -MT"$@" -MT"$(BUILD_DIR)/$(notdir $(<:.cpp=.o))" "$<"


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

.PHONY: all clean tags scope doc seedocp

