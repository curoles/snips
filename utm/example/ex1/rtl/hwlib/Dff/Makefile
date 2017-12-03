
this_dir := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
include $(SOURCE_DIR)/utm/std.makefile

$(call std_prolog)
$(if $(debug_make),$(info $(sp).Makefile))

V_SRC := Dff.v
V_TRG := $(call sv_target,$(V_SRC))

VHDL_SRC := Dff.vhdl
VHDL_TRG := $(call sv_target,$(VHDL_SRC))

targets += $(V_TRG) $(VHDL_TRG)


.PHONY: $(sp)_build
$(sp)_build: $(targets)
	@echo "end of $@: $^"

TEST_SV_SRC := Dff.v Test.sv Dff_checker.sv ../SimClkGen/SimClkGen.sv ../SimRstGen/SimRstGen.sv

.PHONY: $(sp)_unit_test
$(sp)_unit_test: OUTPUT_DIR := $($(sp)_this_build)/unit_test
$(sp)_unit_test: $(addprefix $(this_dir),$(TEST_SV_SRC))
	mkdir -p $(OUTPUT_DIR)
	$(VLOG) $(VLOGFLAGS) -work $(OUTPUT_DIR)/work $(filter %.v %.sv,$^)
#	$(VCOM) $(VHDLFLAGS) -work $(OUTPUT_DIR)/work $(filter %.vhdl,$^)
	$(VSIM) -64 -l vsim.log -lib $(OUTPUT_DIR)/work -c -do "run -all;quit -f" Dve

$(call std_epilog)
