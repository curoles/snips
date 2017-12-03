# author Igor Lesik 2013

all: sim

REL_PATH := $(dir $(lastword $(MAKEFILE_LIST)))

include $(REL_PATH)/../../script/common.mk 

ifeq "$(OS)" "Windows_NT"
  include $(REL_PATH)/../../../config/user/win/env.mk 
else
  include $(REL_PATH)/../../../config/user/unix/env.mk 
endif


BLD := $(BUILD_DIR)/prj/mig1

WORK_NAME  := work
WORK_DIR   := $(BLD)/$(WORK_NAME)

PROGRAM_IMAGE := $(BLD)/memory.txt

VLOG_PARAMS := -work $(WORK_DIR) -l $(BLD)/vlog.log
VLOG_PARAMS += -64
VLOG_PARAMS += +incdir+$(REL_PATH)/rtl

VLOG_PARAMS += +define+MEM_FILE="\"$(PROGRAM_IMAGE)\""


SOURCES := $(REL_PATH)/dv/Dve.sv
SOURCES += $(REL_PATH)/../../hwlib/SimClkGen/model/v/SimClkGen.v
SOURCES += $(REL_PATH)/../../hwlib/Bus/model/v/Bus.v
SOURCES += $(REL_PATH)/../../hwlib/Rom/model/v/Rom.v
SOURCES += $(REL_PATH)/rtl/Mig1.v
SOURCES += $(REL_PATH)/rtl/ProgramCounter.v
SOURCES += $(REL_PATH)/rtl/FrontEnd.v
SOURCES += $(REL_PATH)/rtl/Executor.v

VSIM_RUN_SCRIPT := $(REL_PATH)/dv/runsim.do

VSIM_ARGS := -c -vopt -voptargs="+acc"
#+access +r -t 1ns
VSIM_ARGS += -do $(VSIM_RUN_SCRIPT) -l $(BLD)/vsim.log -lib $(WORK_DIR)
VSIM_ARGS += Dve

#ifdef QUESTA
VSIM_QUESTA_WAVE_DUMP := -wlf $(BLD)/mig1.wlf -wlftlim 5000 -wlfslim 1000
VSIM_ARGS += $(VSIM_QUESTA_WAVE_DUMP)

#ifdef $(ACTIVE_HDL)
#VSIM_ARGS += -asdb $(BLD)/wave.asbd
#endif

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

post_analysis_tools:
	$(call assert-not-null,VSIM_LAUNCHER)
	$(shell echo "$(VSIM_LAUNCHER) -view $(BLD)/mig1.wlf" > $(BLD)/view_wave.sh)
	$(shell chmod a+x $(BLD)/view_wave.sh)

sim: rtl_compile program_compile post_analysis_tools
	$(call assert-not-null,VSIM)
	$(call assert-not-null,VSIM_LAUNCHER)
	$(VSIM_LAUNCHER) $(VSIM_ARGS)

program_compile:
	$(shell echo 00000000 >  $(PROGRAM_IMAGE))
	$(shell echo 00000001 >> $(PROGRAM_IMAGE))
	$(shell echo 00000010 >> $(PROGRAM_IMAGE))
	$(shell echo 00000011 >> $(PROGRAM_IMAGE))
	$(shell echo 00000100 >> $(PROGRAM_IMAGE))
	$(shell echo 00000101 >> $(PROGRAM_IMAGE))
	$(shell echo 00000110 >> $(PROGRAM_IMAGE))


.PHONY: all sim rtl_compile program_compile post_analysis_tools
