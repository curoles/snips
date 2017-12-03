EDA_LICENSE_MENTOR1 := 1717@sv1.smi.local:1717@sv3.smi.local:1717@sv4.smi.local
EDA_LICENSE_MENTOR2 := 1717@login1.smi.local:1717@sge1.smi.local
EDA_LICENSE_MENTOR  := $(EDA_LICENSE_MENTOR1):$(EDA_LICENSE_MENTOR2)

EDA_LICENSE_EVE    := 7280@sv3.smi.local
EDA_LICENSE_XILINX := 2100@sv3.smi.local

# LM_LICENSE_FILE =
EDA_LICENSES := $(EDA_LICENSE_MENTOR)

EDA_TOOLS_HOME  := /tools
EDA_QUESTA_HOME := $(EDA_TOOLS_HOME)/mentor/questa/10.1c/questasim

# All Mentor tools are symlinks to vco script that fails to discover correct
# Linux version and therefore fails to select correct folder with the binaries.
# For now we are forcing where to take the tools (linux_x86_64).
# EDA_QUESTA_BIN := "${DV_HOME_QUESTA}/bin"
EDA_QUESTA_BIN := $(EDA_QUESTA_HOME)/linux_x86_64

#set(ZEBU_ROOT "${DV_HOME_TOOLS}/eve/zebu/V6_3_2B_05")
#set(ZEBU_SYS_DIR "${DV_HOME_TOOLS}/eve/zebu/SYSTEM_DIR_632B")

VLIB := $(EDA_QUESTA_BIN)/vlib
VLOG := $(EDA_QUESTA_BIN)/vlog
VOPT := $(EDA_QUESTA_BIN)/vopt
VSIM := $(EDA_QUESTA_BIN)/vsim

VSIM_LAUNCHER := env LM_LICENSE_FILE="$(EDA_LICENSES)" $(VSIM)

show_eda_settings:
	@echo "Licenses:"
	@echo "Mentor: $(EDA_LICENSE_MENTOR)"
	@echo "EVE   : $(EDA_LICENSE_EVE)"
	@echo "Xilinx: $(EDA_LICENSE_XILINX)"
	@echo "Path:"
	@echo "Questa: $(EDA_QUESTA_BIN)"

