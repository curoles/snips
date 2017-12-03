JFLAGS = -g -Werror
JC = javac

BLD_DIR := ../../build/jui

.SUFFIXES: .java .class

%.class: %.java
	$(JC) $(JFLAGS) -d $(BLD_DIR) -s $(BLD_DIR) $<

CLASSES := POApp.java LoginDialog.java POMainPanel.java
CLASSES += POPeoplePanel.java

default: classes

classes: $(CLASSES:.java=.class)

clean:
	$(RM) $(BLD_DIR)/*.class

.PHONY: default clean
