
this_dir := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
include $(SOURCE_DIR)/utm/std.makefile

$(call std_prolog)
$(if $(debug_make),$(info $(sp).Makefile))

SV_SRC := Memory.sv Sram.sv SparseMem.sv Test.sv
SV_TRG := $(call sv_target,$(SV_SRC))

targets += $(SV_TRG)


.PHONY: $(sp)_build
$(sp)_build: $(targets)
	@echo "end of $@: $^"

TEST_SV_SRC := Memory.sv Sram.sv SparseMem.sv Test.sv

.PHONY: $(sp)_unit_test
$(sp)_unit_test: OUTPUT_DIR := $($(sp)_this_build)/unit_test
$(sp)_unit_test: $(addprefix $(this_dir),$(TEST_SV_SRC))
	mkdir -p $(OUTPUT_DIR)
	$(VLOG) $(VLOGFLAGS) -work $(OUTPUT_DIR)/work $^
	$(VSIM) -64 -l vsim.log -lib $(OUTPUT_DIR)/work -c -do "run -all;quit -f" Dve

$(call std_epilog)
