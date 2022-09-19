# A recursive function that allows to list all files with a given extension,
# in folders and sub-folders, from a given source.
rwildcard=$(wildcard $1$2) $(foreach d,$(wildcard $1*),$(call rwildcard,$d/,$2))

SRCDIR = src
SRC := $(call rwildcard,$(SRCDIR),*.agda)

AGDA ?= agda
AGDAVER = $(subst Agda version ,,$(shell $(AGDA) --version))
AGDAFLAGS ?=

FLAGS ::= \
	--compile-dir=$(SRCDIR)/ \
	--ghc \
	--ghc-dont-call-ghc \
	--no-main \
	-W all \
	-i $(SRCDIR) \
	-l standard-library \
	-l agda-prelude \
	-W noCoverageNoExactSplit \
	-W noUnknownFixityInMixfixDecl \
	-W noShadowingInTelescope \
	$(AGDAFLAGS)

all: $(addsuffix i, $(SRC))

%.agdai: %.agda
	$(info ‣ $<)
	@$(AGDA) $(FLAGS) $<

.PHONY: clean
clean:
	-@(yes | rm $(SRCDIR)/MAlonzo -r 2>/dev/null)
# In case we are not using --local-interfaces:
	-@rm _build -r 2>/dev/null
# In case we are using --local-interfaces:
# Beware that 'rwildcard' may return nothing, which 'rm' is not happy about
	-@rm $(call rwildcard,$(SRCDIR),*.agdai) 2>/dev/null