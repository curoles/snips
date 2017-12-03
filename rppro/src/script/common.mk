# Here is an easy way to test whether the makefile is running on Windows.
# Look for the COMSPEC environment variable defined only on Windows:
PATH_SEP := $(if $(COMSPEC),;,:)
# Now PATH_SEP contains the proper character to use in paths,
# whether the makefile is running on Windows or Unix

# $(call assert,condition,message)
define assert
  $(if $1,,$(error Assertion failed: $2))
endef
# $(call assert-file-exists,wildcard-pattern)
define assert-file-exists
  $(call assert,$(wildcard $1),$1 does not exist)
endef
# $(call assert-not-null,make-variable)
define assert-not-null
  $(call assert,$($1),The variable "$1" is null)
endef
#error-exit:
#        $(call assert-not-null,NON_EXISTENT)

