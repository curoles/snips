
this_dir := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
include $(SOURCE_DIR)/utm/std.makefile

$(call std_prolog)
$(if $(debug_make),$(info $(sp).Makefile))

SV_SRC := ../hvlib/stdtype.sv TbTop.sv
SV_TRG := $(call sv_target,$(SV_SRC))

targets += $(SV_TRG)


.PHONY: $(sp)_build
$(sp)_build: $(targets)
	@echo "end of $@: $^"

TEST_SV_SRC := ../hvlib/stdtype.sv TbTop.sv
TEST_SV_SRC += ../../rtl/hwlib/SimClkGen/SimClkGen.sv ../../rtl/hwlib/SimRstGen/SimRstGen.sv

.PHONY: $(sp)_test_bench
$(sp)_test_bench: OUTPUT_DIR := $($(sp)_this_build)/test_bench
$(sp)_test_bench: $(addprefix $(this_dir),$(TEST_SV_SRC))
	mkdir -p $(OUTPUT_DIR)
	$(VLOG) $(VLOGFLAGS) -work $(OUTPUT_DIR)/work $^
	$(VSIM) -64 -l vsim.log -lib $(OUTPUT_DIR)/work -c -do "run -all;quit -f" E1TbTop

$(call std_epilog)
