$(if $(debug_make),$(info dv.Component.makefile))

this_dir := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
include $(SOURCE_DIR)/utm/std.makefile

$(call std_prolog)

.PHONY: $(sp)_build
$(sp)_build: $(targets)
	@echo "end of $@: $^"

$(call std_epilog)

