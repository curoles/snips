SAVED_REL_PATH := $(REL_PATH)

REL_PATH := $(dir $(lastword $(MAKEFILE_LIST)))

BUILD_DIR := C:\Users\igor\Projects\rppro\build

GNU_TOOLS ?= c:\tools\gnu\bin
MKDIR := $(GNU_TOOLS)/mkdir.exe

ACTIVE_HDL_INSTALL_PATH := C:\Program Files (x86)\Aldec\Active-HDL 8.2

include $(REL_PATH)/../../tools/win/ActiveHDL_8_2.mk

REL_PATH := $(SAVED_REL_PATH)
