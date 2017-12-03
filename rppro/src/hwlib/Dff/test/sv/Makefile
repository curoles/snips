# author Igor Lesik 2013

all: sim

REL_PATH := $(dir $(lastword $(MAKEFILE_LIST)))

include $(REL_PATH)/../../../../script/common.mk 

ifeq "$(OS)" "Windows_NT"
  include $(REL_PATH)/../../../../../config/user/win/env.mk 
else
  include $(REL_PATH)/../../../../../config/user/unix/env.mk 
endif


# BUILD_DIR ?= $(REL_PATH)/../../../../../../build

BLD := $(BUILD_DIR)/test/hwlib/Dff/sv

WORK_NAME  := work
WORK_DIR   := $(BLD)/$(WORK_NAME)

VLOG_PARAMS := -work $(WORK_DIR) -l $(BLD)/vlog.log
VLOG_PARAMS += -64

#VFLAGS := -o $(BUILD_DIR) -work $(WORK_NAME) -dbg

SOURCES := $(REL_PATH)/Dve.sv $(REL_PATH)/../../model/v/Dff.v

VSIM_RUN_SCRIPT := $(REL_PATH)/runsim.do

VSIM_ARGS := -c +access +r -t 1ps
VSIM_ARGS += -do $(VSIM_RUN_SCRIPT) -l $(BLD)/vsim.log -lib $(WORK_DIR)
VSIM_ARGS += Dve

ifdef $(ACTIVE_HDL)
VSIM_ARGS += -asdb $(BLD)/wave.asbd
endif

$(BUILD_DIR):
	$(call assert-not-null,MKDIR)
	$(MKDIR) -p $@

$(WORK_DIR): $(BUILD_DIR)
	$(MKDIR) -p $(dir $@)
	$(call assert-not-null,VLIB)
	$(VLIB) $@ 

rtl_compile: $(WORK_DIR)
	$(call assert-not-null,MKDIR)
	$(VLOG) $(VLOG_PARAMS) $(SOURCES)

sim: rtl_compile
	$(call assert-not-null,VSIM)
	$(VSIM_LAUNCHER) $(VSIM_ARGS)

.PHONY: all sim rtl_compile
