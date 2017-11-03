# Main make file.
# Author: Igor Lesik 2017

.PHONY: all
all: build_site
	@echo All done!

#include $(SOURCE_PATH)/build/get_tools.makefile

.PHONY: build_site
build_site: build_opts=--clean --verbose --build-dir=$(BUILD_DIR)/website
build_site:
	cd $(SOURCE_PATH)/site && NO_CONTRACTS=true bundle exec middleman build $(build_opts)

