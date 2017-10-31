MDWIKI_VER := 0.6.2
MDWIKI_ZIP := mdwiki-$(MDWIKI_VER).zip
MDWIKI_URL := "https://github.com/Dynalon/mdwiki/releases/download/$(MDWIKI_VER)/$(MDWIKI_ZIP)"

$(MDWIKI_ZIP):
	wget $(MDWIKI_URL)

mdwiki: $(MDWIKI_ZIP)
	unzip -d $@ $(MDWIKI_ZIP)

example: $(SOURCE_PATH)/example
	cp -r $(SOURCE_PATH)/example ./

example/index.html: example
example/index.html: MDWIKI_HTML=mdwiki/mdwiki-$(MDWIKI_VER)/mdwiki.html
example/index.html:
	cp $(MDWIKI_HTML) $@
#example/index.html: TARGET=mdwiki/mdwiki-$(MDWIKI_VER)/mdwiki.html
#example/index.html: $(SOURCE_PATH)/example/redirect.html
#	sed 's|TARGET|$(TARGET)|g' < $(SOURCE_PATH)/example/redirect.html > $@

.PHONY: get_tools
get_tools: mdwiki example/index.html
	@echo Got external tools
