SRC_DIR := $(SOURCE_PATH)/src
OBJ_DIR := $(BUILD_DIR)/obj

.PHONY: all
all: $(OBJ_DIR)/igr

CFLAGS := $(CFLAGS) -Wall -Werror -fopenmp

$(OBJ_DIR)/%.o : $(SRC_DIR)/%.c
	mkdir -p $(@D)
	$(CC) $(CFLAGS) -MMD -c $< -o $@

SRCs := 
SRCs += alloc.c string.c sym.c
SRCs += back/x86_gas.c
SRCs += selfcheck.c
SRCs += print.c
SRCs += options.c
SRCs += igr.c

SRCS := $(addprefix $(SRC_DIR)/,$(SRCs))

OBJs := $(SRCs:.c=.o)
OBJS := $(addprefix $(OBJ_DIR)/,$(OBJs))
DEPS := $(OBJS:.o=.d)

$(OBJ_DIR)/igr : $(OBJS)
	# Link all the object files.
	$(CC) $(CFLAGS) $^ -o $@

$(OBJ_DIR):
	mkdir -p $(OBJ_DIR)

.PHONY: clean
clean:
	rm -rf $(OBJ_DIR)

-include $(DEPS)

include $(SOURCE_PATH)/bld/doc.makefile
