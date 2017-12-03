ERLANG_SRC_DIR := $(SOURCE_PATH)/src/erlang
ERLANG_BUILD_DIR := ./build/erlang


$(ERLANG_BUILD_DIR):
	mkdir -p $(ERLANG_BUILD_DIR)

ERLANG_SRCs := bmb_util.erl
ERLANG_SRCs += bumbler.erl bumbler_app.erl bmb_msg_server.erl
ERLANG_SRCs += bmb_msg_gate.erl bmb_gate_factory.erl
ERLANG_SRCs += domain/internal/bmb_internal_domain.erl
ERLANG_SRCs += domain/internal/bmb_echo_client.erl
ERLANG_SRCs += domain/tcp/bmb_tcp_domain.erl
ERLANG_SRCs += client/terminal_client/bmb_terminal_client.erl
ERLANG_SRCs += client/terminal_client/bmb_terminal_client_app.erl

# Erlang source files with the path.
ERLANG_SRCS := $(addprefix $(ERLANG_SRC_DIR)/,$(ERLANG_SRCs))

ERLANG_OBJs := $(ERLANG_SRCs:.erl=.beam)
ERLANG_OBJS := $(addprefix $(ERLANG_BUILD_DIR)/,$(ERLANG_OBJs))

.PHONY: erlang
erlang: $(ERLANG_BUILD_DIR) $(ERLANG_OBJS) $(ERLANG_SRCS)


.PHONY: erlang_docs
erlang_docs: QCQ := \",\"
erlang_docs: EDOC_FILES := $(addprefix $(ERLANG_SRC_DIR)/,overview.edoc)
erlang_docs: SRC_LIST := '[\"$(subst $(SPACE),$(QCQ),$(ERLANG_SRCS))\"]'
erlang_docs: $(ERLANG_SRCS)
	$(ERL) -noshell -run edoc_run files '$(SRC_LIST)' '[{dir,"./build/docs/erlang"}]'

# http://erlang.org/doc/system_principles/system_principles.html#code_loading
#$(INSTALL_PATH)/run_server.bash: ERL_INIT_DEBUG := -init_debug
#$(INSTALL_PATH)/run_server.bash: ERL_MODE := -mode embedded
$(INSTALL_PATH)/run_server.bash: $(INSTALL_PATH)
	echo "#!/bin/bash" > $@
	echo "BOOT_OPTIONS=\"-name bumbler -boot start_sasl -s bumbler start\"" >> $@
	echo "CODE_PATH=\"-pa $(ERLANG_BUILD_DIR) -pz $(ERLANG_BUILD_DIR)/domain/internal \"" >> $@
	echo "CODE_PATH=\" \$${CODE_PATH} -pz $(ERLANG_BUILD_DIR)/domain/tcp \"" >> $@
	echo "$(ERL) $(ERL_MODE) $(ERL_INIT_DEBUG) \$${CODE_PATH} \$${BOOT_OPTIONS}" >> $@

$(INSTALL_PATH)/run_terminal_client.bash: $(INSTALL_PATH)
	echo "#!/bin/bash" > $@
	echo "BOOT_OPTIONS=\"-name terminal_client -boot start_sasl -s bmb_terminal_client start\"" >> $@
	echo "CODE_PATH=\"-pa $(ERLANG_BUILD_DIR)/client/terminal_client \"" >> $@
	echo "$(ERL) $(ERL_MODE) $(ERL_INIT_DEBUG) \$${CODE_PATH} \$${BOOT_OPTIONS}" >> $@



.PHONY: install_app_desc
install_app_desc: $(ERLANG_BUILD_DIR)/bumbler_app.app
install_app_desc: $(ERLANG_BUILD_DIR)/client/terminal_client/bmb_terminal_client_app.app

$(ERLANG_BUILD_DIR)/bumbler_app.app: $(ERLANG_SRC_DIR)/bumbler_app.app
	cp $< $@

$(ERLANG_BUILD_DIR)/client/terminal_client/bmb_terminal_client_app.app: $(ERLANG_SRC_DIR)/client/terminal_client/bmb_terminal_client_app.app
	cp $< $@


