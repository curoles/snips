SCALA_VER := 2.12
AKKA_JAR := akka-actor_$(SCALA_VER)-2.5.0.jar
CONF_JAR := config-1.3.1.jar
AKKA_CAMEL_JAR := akka-camel_$(SCALA_VER)-2.5.0.jar
AKKA_STREAM_JAR := akka-stream_$(SCALA_VER)-2.5.0.jar

EXT_JARS := $(AKKA_JAR):$(CONF_JAR):$(AKKA_CAMEL_JAR)

.PHONY: compile
compile: get_jars
	scalac -classpath $(EXT_JARS) -d class BattleField.scala

.PHONY: get_jars
get_jars: $(AKKA_JAR) $(CONF_JAR) $(AKKA_CAMEL_JAR)

$(CONF_JAR):
	wget http://central.maven.org/maven2/com/typesafe/config/1.3.1/$(CONF_JAR)

$(AKKA_JAR):
	wget http://repo1.maven.org/maven2/com/typesafe/akka/akka-actor_$(SCALA_VER)/2.5.0/$(AKKA_JAR)

$(AKKA_CAMEL_JAR):
	wget http://repo1.maven.org/maven2/com/typesafe/akka/akka-camel_$(SCALA_VER)/2.5.0/$(AKKA_CAMEL_JAR)

$(AKKA_STREAM_JAR):
	wget http://repo1.maven.org/maven2/com/typesafe/akka/akka-stream_$(SCALA_VER)/2.5.0/$(AKKA_STREAM_JAR)

.PHONY: run
run:
	scala -classpath $(AKKA_JAR):$(CONF_JAR):./class  BattleFieldGame
