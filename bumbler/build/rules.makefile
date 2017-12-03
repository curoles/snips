
ifndef ERLC
$(error ERLC is not defined)
endif

ERLC_FLAGS := -Wall -Werror -v
ERLC_INCLUDES := -I $(ERLANG_SRC_DIR)

$(ERLANG_BUILD_DIR)/%.beam : $(ERLANG_SRC_DIR)/%.erl
	@mkdir -p $(@D)
	$(ERLC) $(ERLC_FLAGS) $(ERLC_INCLUDES) -o $(@D) $<


ifndef JAVAC
$(error JAVAC is not defined)
endif

JAVAC_FLAGS := -cp $(JAVA_BUILD_DIR) 

#$(JAVA_BUILD_DIR)/%.class : $(JAVA_SRC_DIR)/%.java
#	mkdir -p $(@D)
#	$(JAVAC) $(JAVAC_FLAGS) -d $(@D) $<

$(JAVA_BUILD_DIR)/%.class : $(JAVA_SRC_DIR)/%.java
	$(JAVAC) $(JAVAC_FLAGS) -d $(JAVA_BUILD_DIR) $<

ifndef SCALAC
$(error SCALAC is not defined)
endif

SCALAC_FLAGS := -cp "$(SCALA_CLASS_DIR):$(SCALA_EXTRA_LIB_DIR)/*"
SCALAC_FLAGS += -Xlint

THE_SCALAC := $(FASTSCALAC)

$(SCALA_CLASS_DIR)/%.class : $(SCALA_SRC_DIR)/%.scala
	$(THE_SCALAC) $(SCALAC_FLAGS) -d $(SCALA_CLASS_DIR) $<

