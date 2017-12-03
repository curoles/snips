$(info Build.makefile)

#MAKEFILES ?= --output-sync=target

include $(SOURCE_DIR)/utm/BuildRules.makefile


.PHONY: all
all: $(BUILD_DIR)/default_vlog_build/work .rtl_build .dv_build

$(BUILD_DIR)/default_vlog_build/work:
	mkdir -p $(BUILD_DIR)/default_vlog_build
	$(VLIB) $@


include $(SOURCE_DIR)/rtl/Component.makefile
include $(SOURCE_DIR)/dv/Component.makefile

.PHONY: clean
clean:
	find ./* ! -name Makefile -exec rm -frv {} +
