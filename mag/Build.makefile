SRC_FILES := main.c write_to_tiff.c image.c

SRC_FILES := $(addprefix $(SOURCE_PATH)/,$(SRC_FILES))

CFLAGS := -Werror -Wall -std=gnu99

LIBS := -ltiff

.PHONY: all
all:
	$(CC) $(CFLAGS) $(SRC_FILES) $(LIBS) -o mag
