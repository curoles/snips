HOSTNAME := $(shell hostname)
$(info Host: $(HOSTNAME))

NATURALDOCS := /home/igor/tool/NaturalDocs/1.52/NaturalDocs
DITAA := /home/igor/tool/ditaa/ditaa
PYGMENTIZE := pygmentize -f html -O full,style=colorful,lineos=inline
DOXYGEN := doxygen
SV_DOXY_FILTER := /home/igor/tool/SVDoxyFilter/2.6.2.r138

-include $(BUILD_DIR)/env.makefile

VSIM_DIR := $(BUILD_DIR)/vsim
DOC_DIR := $(BUILD_DIR)/doc
DOC_FILES_DIR := $(BUILD_DIR)/doc/files


vsources  := rtl/lib/Dff.v rtl/lib/Fifo.v
vsources  += rtl/lib/FullAdder.v rtl/lib/RippleCarryAdder.v
vsources  += rtl/CpuParams.v
vsources  += rtl/ifu/IFU.v rtl/MigCpu.v rtl/Dut.v
svsources := rtl/lib/stdtype.sv rtl/lib/Helpers.sv
svsources += dv/lib/SimClkGen.sv dv/lib/SimRstGen.sv
svsources += dv/DefaultAssertClkBlock.sv
svsources += dv/mem/Memory.sv dv/mem/Sram.sv dv/mem/SimRam.sv
svsources += dv/DutTop.sv dv/TbTop.sv

$(VSIM_DIR)/dv/DutTop.sv.vsim : $(VSIM_DIR)/rtl/lib/stdtype.sv.vsim
$(VSIM_DIR)/rtl/ifu/IFU.v.vsim : $(VSIM_DIR)/rtl/lib/Helpers.sv.vsim
$(VSIM_DIR)/rtl/lib/Helpers.sv.vsim : $(VSIM_DIR)/rtl/lib/stdtype.sv.vsim

vtargets := $(patsubst %.v,$(VSIM_DIR)/%.v.vsim,$(vsources))
vtargets += $(patsubst %.sv,$(VSIM_DIR)/%.sv.vsim,$(svsources))

vhtml_targets := $(patsubst %.v,$(DOC_FILES_DIR)/%.v.html,$(vsources))

.PHONY: all
all:

.PHONY: clean
clean:
	find ./* ! -name Makefile ! -name env.makefile -exec rm -frv {} +

.PHONY: doc
doc: INPUT      := --source $(SOURCE_DIR)
doc: OUTPUT_DIR := $(DOC_DIR)
doc: OUTPUT     := --output HTML $(OUTPUT_DIR)
doc: PROJECT    := --project $(OUTPUT_DIR)
doc: $(vhtml_targets)
	mkdir -p $(OUTPUT_DIR)
	$(NATURALDOCS) $(INPUT) $(OUTPUT) $(PROJECT)

.PHONY: dox
dox: OUTPUT_DIR := $(BUILD_DIR)/dox
dox: DOXY_FILE := $(BUILD_DIR)/dox/Doxyfile
dox: SV_FILTER := $(SV_DOXY_FILTER)/filter/idv_doxyfilter_sv.pl
dox:
	mkdir -p $(OUTPUT_DIR)
	cp $(SOURCE_DIR)/doc/Doxyfile $(DOXY_FILE)
	echo "OUTPUT_DIRECTORY = $(OUTPUT_DIR)" >> $(DOXY_FILE)
	echo "INPUT += $(SOURCE_DIR)" >> $(DOXY_FILE)
	echo "STRIP_FROM_PATH += $(SOURCE_DIR)" >> $(DOXY_FILE)
	echo "FILE_PATTERNS += *.svh *.sv *.v *.vh *.cpp *.c *.h" >> $(DOXY_FILE)
	echo "EXAMPLE_PATTERNS += *.sv, *.svh, *.v, *.vh" >> $(DOXY_FILE)
	echo "EXTENSION_MAPPING += sv=C++ svh=C++ v=C++ vh=C++" >> $(DOXY_FILE)
	echo "FILTER_PATTERNS += *.sv=$(SV_FILTER)" >> $(DOXY_FILE)
	echo "FILTER_PATTERNS += *.svh=$(SV_FILTER)" >> $(DOXY_FILE)
	echo "FILTER_PATTERNS += *.v=$(SV_FILTER)" >> $(DOXY_FILE)
	echo "FILTER_PATTERNS += *.vh=$(SV_FILTER)" >> $(DOXY_FILE)
	echo "LAYOUT_FILE = $(SV_DOXY_FILTER)/doxyfile/idv_doxylayout.xml" >> $(DOXY_FILE)
	$(DOXYGEN) $(DOXY_FILE)


include $(SOURCE_DIR)/build/MentorEnv.makefile
include $(SOURCE_DIR)/build/SynopsysEnv.makefile

VLOGFLAGS += +define+SV_ENABLED -sv
VLOGFLAGS += +incdir+$(SOURCE_DIR)
 
$(VSIM_DIR)/%.sv.vsim : $(SOURCE_DIR)/%.sv
	mkdir -p $(@D)
	$(VLOG) $(VLOGFLAGS) -work $(BUILD_DIR)/work $<
	touch $@

$(VSIM_DIR)/%.v.vsim : $(SOURCE_DIR)/%.v
	mkdir -p $(@D)
	$(VLOG) $(VLOGFLAGS) -work $(BUILD_DIR)/work $<
	touch $@

$(DOC_FILES_DIR)/%.v.html : $(SOURCE_DIR)/%.v
	mkdir -p $(@D)
	$(PYGMENTIZE) -l verilog -o $@ $<
	cd $(@D) && $(DITAA) --html $< -o $@.diag 

#$(info Verilog targets: $(vtargets))

.PHONY: vlog
vlog: $(vtargets)

.PHONY: vopt
vopt: vlog
	$(VOPT) -64 -l vopt.log -work $(BUILD_DIR)/work DutTop TbTop -o Design

.PHONY: vsim
vsim: vopt
	$(VSIM) -64 -l vsim.log -lib $(BUILD_DIR)/work -c -do "run -all;quit -f" Design

.PHONY: spyglass
spyglass:
	$(SPYGLASS) $(SPYGLASS_FLAGS)

