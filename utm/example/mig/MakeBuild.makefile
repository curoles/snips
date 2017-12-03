#// File: MakeBuild.makefile
#//
#// About:
#//   Author - Igor Lesik 2015-16

#http://blog.melski.net/2013/11/29/whats-new-in-gnu-make-4-0/

$(info This makefile generates build infra, call it like this from a build directory:)
$(info make -f <source path>/MakeBuild.makefile)
$(info )
$(info make version $(MAKE_VERSION))
$(info )

REQUIRE_MAKE_VER := 4.0
MAKE_VER_OK := $(filter $(REQUIRE_MAKE_VER),$(firstword $(sort $(MAKE_VERSION) $(REQUIRE_MAKE_VER))))

ifeq ($(strip $(MAKE_VER_OK)),)
  $(error Required make version is $(REQUIRE_MAKE_VER))
endif

BUILD_DIR   := $(abspath $(CURDIR))

MKFILE_PATH := $(abspath $(lastword $(MAKEFILE_LIST)))
SOURCE_DIR  := $(dir $(MKFILE_PATH))

$(info Build dir    : $(BUILD_DIR))
$(info Makefile path: $(MKFILE_PATH))
$(info Source dir   : $(SOURCE_DIR))
$(info )

#.ONESHELL:
all: clean
	$(call generate_build_infra)

clean:
	@rm -rf ./*

define generate_build_infra
  $(info Generating build infra...)
  $(file >Makefile,# Main makefile)
  $(call generate_main_makefile,Makefile)
  $(info Makefile is generated, you can call make now.)
endef

define check-make-version =

REQUIRE_MAKE_VER := 4.0
MAKE_VER_OK := $$(filter $$(REQUIRE_MAKE_VER),$$(firstword $$(sort $$(MAKE_VERSION) $$(REQUIRE_MAKE_VER))))

ifeq ($$(strip $$(MAKE_VER_OK)),)
  $$(info MAKE version $$(MAKE_VERSION)...[ERROR])
  $$(error Required make version is $$(REQUIRE_MAKE_VER))
else
  $$(info MAKE version $$(MAKE_VERSION)...[OK])
endif

endef

define generate_main_makefile
  $(eval file_name := $1)
  $(file >>$(file_name),# Automatically generated on $(shell date))
  $(file >>$(file_name),)
  $(file >>$(file_name),$(check-make-version))
  $(file >>$(file_name),)
  $(file >>$(file_name),BUILD_DIR := $(BUILD_DIR))
  $(file >>$(file_name),SOURCE_DIR := $(SOURCE_DIR))
  $(file >>$(file_name),)
  $(file >>$(file_name),include $$(SOURCE_DIR)/build/Makefile)
endef

.PHONY: all clean

