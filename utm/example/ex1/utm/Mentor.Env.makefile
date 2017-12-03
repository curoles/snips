
MGLIC1 := 1717@sv13.smi.local:1717@sv7.smi.local:1717@sv6.smi.local:1717@sv5.smi.local
MGLIC2 := 1717@sv20.smi.local:1717@sv15.smi.local:1717@sv21.smi.local:1717@sv24.smi.local
MGLIC3 := 1717@sv14.smi.local:1717@sv4.smi.local:1717@sv3.smi.local:1717@sge1.smi.local
MGLIC4 := 1717@sv18.smi.local:1717@sv1.smi.local:1717@sv19.smi.local
MGLIC5 := 1717@sv9.smi.local:1717@sv10.smi.local:1717@sv13.smi.local
MENTOR_LICENSE := $(MGLIC1):$(MGLIC2):$(MGLIC3):$(MGLIC4):$(MGLIC5)

DV_TOOLS_HOME := /tools
MENTOR_HOME :=  /tools/mentor

QUESTA_VERSION := 10.4
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
