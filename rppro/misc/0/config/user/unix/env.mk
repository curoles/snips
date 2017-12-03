SAVED_REL_PATH := $(REL_PATH)

REL_PATH := $(dir $(lastword $(MAKEFILE_LIST)))

BUILD_DIR := /home/igor/prj/rppro/build


MKDIR := mkdir


include $(REL_PATH)/../../tools/unix/Questa.mk

REL_PATH := $(SAVED_REL_PATH)
