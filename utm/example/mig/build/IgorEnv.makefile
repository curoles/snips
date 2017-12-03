# Move it to the build dir and rename to env.makefile

ifeq ($(HOSTNAME),pc104.smi.local)
#NATURALDOCS := /local_disk/igor/tools/NaturalDocs/NaturalDocs1.51/NaturalDocs
DOXYGEN := /tools/local/doxygen-1.8.11/bin/doxygen
$(info DOXYGEN=$(DOXYGEN))
SV_DOXY_FILTER := /local_disk/igor/tools/SVDoxyFilter/2.6.2.r138

else ifeq ($(HOSTNAME),igor-MacPro)
SV_DOXY_FILTER := /home/igor/tools/SVDoxyFilter/2.6.2.r138

endif

