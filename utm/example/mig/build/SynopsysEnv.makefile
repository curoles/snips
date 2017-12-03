
SPYGLASS_HOME := /tools/atrenta/spyglass/5.5.0.2/SpyGlass-5.5.0.2/SPYGLASS_HOME
SPYGLASS := $(SPYGLASS_HOME)/bin/spyglass

ATRENTA_LICENSE_FILE=27050@sge1.smi.local
SPYGLASS := ATRENTA_LICENSE_FILE=$(ATRENTA_LICENSE_FILE) SOURCE_DIR=$(SOURCE_DIR) $(SPYGLASS)

SPYGLASS_FLAGS := -batch -project $(SOURCE_DIR)/build/spyglass.prj -goals lint/lint_rtl
