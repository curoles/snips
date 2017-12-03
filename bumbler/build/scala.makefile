
SCALA_SRC_DIR := $(SOURCE_PATH)/src/scala
SCALA_BUILD_DIR := ./build/scala
SCALA_CLASS_DIR := ./build/scala/class
SCALA_EXTRA_LIB_DIR := ./build/scala/extralib

SCALA_SRCs := 
SCALA_SRCs += Weather.scala TextFile.scala
SCALA_SRCs += Functional.scala
SCALA_SRCs += io/Dir.scala io/File.scala
SCALA_SRCs += Test1.scala
SCALA_SRCs += edc/Edc.scala edc/Simulation.scala edc/Wire.scala edc/Driver.scala
SCALA_SRCs += edc/Circuit1.scala edc/SimRunner.scala

# Scala source files with the path.
SCALA_SRCS := $(addprefix $(SCALA_SRC_DIR)/,$(SCALA_SRCs))

SCALA_OBJs := $(SCALA_SRCs:.scala=.class)
SCALA_OBJS := $(addprefix $(SCALA_CLASS_DIR)/,$(SCALA_OBJs))

.PHONY: scala
scala: $(SCALA_CLASS_DIR) scala_extra_libs $(SCALA_OBJS)

$(SCALA_CLASS_DIR):
	mkdir -p $(SCALA_CLASS_DIR)

$(SCALA_EXTRA_LIB_DIR):
	mkdir -p $(SCALA_EXTRA_LIB_DIR)

.PHONY: scala_extra_libs
scala_extra_libs: $(SCALA_EXTRA_LIB_DIR)/scalatest_2.11-3.0.0.jar
scala_extra_libs: $(SCALA_EXTRA_LIB_DIR)/scalactic_2.11-3.0.0.jar

$(SCALA_EXTRA_LIB_DIR)/scalatest_2.11-3.0.0.jar:
	@mkdir -p $(SCALA_EXTRA_LIB_DIR)
	wget -P $(SCALA_EXTRA_LIB_DIR) https://oss.sonatype.org/content/groups/public/org/scalatest/scalatest_2.11/3.0.0/scalatest_2.11-3.0.0.jar

$(SCALA_EXTRA_LIB_DIR)/scalactic_2.11-3.0.0.jar:
	@mkdir -p $(SCALA_EXTRA_LIB_DIR)
	wget -P $(SCALA_EXTRA_LIB_DIR) https://oss.sonatype.org/content/groups/public/org/scalactic/scalactic_2.11/3.0.0/scalactic_2.11-3.0.0.jar

.PHONY: scala_docs
scala_docs: SCALAC_FLAGS := -cp "$(SCALA_EXTRA_LIB_DIR)/*"
scala_docs: $(SCALA_SRCS)
	mkdir -p ./build/docs/scala
	scaladoc -d ./build/docs/scala $(SCALAC_FLAGS) $(SCALA_SRCS)


