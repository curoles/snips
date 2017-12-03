DOCS_BUILD_DIR := ./build/docs
MAIN_DOCS_BUILD_DIR := $(DOCS_BUILD_DIR)/main
ERLANG_DOCS_BUILD_DIR := $(DOCS_BUILD_DIR)/erlang

.PHONY: main_docs
main_docs: DOXY_CFG := SOURCE_PATH=$(SOURCE_PATH) OUTPUT_DIR=$(MAIN_DOCS_BUILD_DIR)
main_docs: $(MAIN_DOCS_BUILD_DIR)
	$(DOXY_CFG) doxygen $(SOURCE_PATH)/docs/Doxyfile

$(MAIN_DOCS_BUILD_DIR):
	mkdir -p $(MAIN_DOCS_BUILD_DIR)

.PHONY: docs
docs: main_docs erlang_docs
