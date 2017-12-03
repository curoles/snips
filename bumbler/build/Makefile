# author: Igor Lesik
# copyright: Igor Lesik 2016
#


INSTALL_PATH := ./install

EMPTY :=
SPACE := $(EMPTY) $(EMPTY)

include $(SOURCE_PATH)/build/erlang.makefile
include $(SOURCE_PATH)/build/java.makefile
include $(SOURCE_PATH)/build/scala.makefile
include $(SOURCE_PATH)/build/rules.makefile
include $(SOURCE_PATH)/build/docs.makefile


$(INSTALL_PATH):
	mkdir -p $(INSTALL_PATH)


.PHONY: build_all
build_all: erlang java

.PHONY: install_scripts
install_scripts: $(INSTALL_PATH)/java_client.bash
install_scripts: $(INSTALL_PATH)/run_server.bash $(INSTALL_PATH)/run_terminal_client.bash 

.PHONY: installation
installation: build_all install_scripts install_app_desc

.PHONY: all
all: installation


