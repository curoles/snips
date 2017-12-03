$(if $(debug_make),$(info rtl.Component.makefile))

this_dir := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
include $(SOURCE_DIR)/utm/std.makefile

$(call std_prolog)

.PHONY: $(sp)_build
$(sp)_build: $(targets)
	@echo "making $@: $^"

$(call std_epilog)
