# Main make file.
# Author: Igor Lesik 2017

.PHONY: all
all: build_site
	@echo All done!

WEBSITE_DIR := $(BUILD_DIR)/website

.PHONY: build_site
build_site: build_opts=--clean --verbose --build-dir=$(WEBSITE_DIR)
build_site:
	cd $(SOURCE_PATH)/site && NO_CONTRACTS=true bundle exec middleman build $(build_opts)

.PHONY: run_py_server
run_py_server:
	cd $(WEBSITE_DIR) && python3 -m http.server

.PHONY: api
api:
	yard doc $(SOURCE_PATH)/tools/**/*.rb -o $(WEBSITE_DIR)/pages/api

.PHONY: show_gems
show_gems:
	cd $(SOURCE_PATH)/site && bundle show
	gem search ^middleman$$
	gem search ^middleman-autoprefixer$$
	gem search ^middleman-blog$$
	gem search ^tzinfo-data$$
	gem search ^wdm$$
	gem search ^bh$$
