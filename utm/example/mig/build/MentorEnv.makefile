
MGLIC1 := 1717@sv13.smi.local:1717@sv7.smi.local:1717@sv6.smi.local:1717@sv5.smi.local
MGLIC2 := 1717@sv20.smi.local:1717@sv15.smi.local:1717@sv21.smi.local:1717@sv24.smi.local
MGLIC3 := 1717@sv14.smi.local:1717@sv4.smi.local:1717@sv3.smi.local:1717@sge1.smi.local
MGLIC4 := 1717@sv18.smi.local:1717@sv1.smi.local:1717@sv19.smi.local
MGLIC5 := 1717@sv9.smi.local:1717@sv10.smi.local:1717@sv13.smi.local
MENTOR_LICENSE := $(MGLIC1):$(MGLIC2):$(MGLIC3):$(MGLIC4):$(MGLIC5)

DV_TOOLS_HOME := /tools
MENTOR_HOME :=  /tools/mentor

QUESTA_VERSION := 10.5
QUESTA_HOME := $(MENTOR_HOME)/questa/$(QUESTA_VERSION)/questasim

QUESTA_DIR := $(QUESTA_HOME)/linux_x86_64
#VISUAL_DIR ${VISUAL_HOME}/linux_x86_64)

VLIB := $(QUESTA_DIR)/vlib
VMAP := $(QUESTA_DIR)/vmap
VLOG := $(QUESTA_DIR)/vlog
VCOM := $(QUESTA_DIR)/vcom
VOPT := $(QUESTA_DIR)/vopt
VSIM := LM_LICENSE_FILE=$(MENTOR_LICENSE) $(QUESTA_DIR)/vsim

VLOGFLAGS := -64 -time -pedanticerrors -sfcu -lint -warning error
VHDLFLAGS := -64 -time -pedanticerrors -lint -warning error
VOPTFLAGS := -64

#set(DV_TOOLS_HOME  /tools)
#set(MENTOR_HOME    /tools/mentor)
#
#set(QUESTA_VERSION 10.4d)
#set(QUESTA_HOME    ${MENTOR_HOME}/questa/${QUESTA_VERSION}/questasim)
#
#set(VISUAL_VERSION 10.4d)
#set(VISUAL_HOME    ${MENTOR_HOME}/visualizer/${VISUAL_VERSION}/visualizer)
#
#set(VELOCE_VERSION v2.1.1.24)
#set(VELOCE_HOME    ${MENTOR_HOME}/veloce/Veloce_${VELOCE_VERSION})
#
#set(TBX_VERSION    v2.4.4.18)
#set(TBX_HOME       ${MENTOR_HOME}/TBX/TBX_${TBX_VERSION})
#
#set(VELOCE_XACTOR_HOME ${MENTOR_HOME}/veloce_transactor_library/Veloce_Transactors_Library_v3.0.1.0)

