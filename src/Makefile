FSTAR_FILES=$(wildcard *.fst)
# FSTAR_FILES=$(shell find asn1/ -type f -name '*.fst')

OUTPUT_DIR=obj

EVERPARSE_HOME ?= $(SOURCES_HOME)/everparse

FSTAR_INCLUDES=$(FSTAR_HOME)/ulib/.cache \
  $(KREMLIN_HOME)/include \
  $(KREMLIN_HOME)/kremlib/dist/generic \
  $(HACL_HOME)/specs \
  $(HACL_HOME)/specs/lemmas \
  $(HACL_HOME)/specs/ecdsap256sha2 \
  $(HACL_HOME)/vale/specs/hardware \
  $(HACL_HOME)/vale/specs/defs \
  $(HACL_HOME)/code/meta \
  $(HACL_HOME)/code/hash \
  $(HACL_HOME)/code/hkdf \
  $(HACL_HOME)/code/hmac\
  $(HACL_HOME)/code/curve25519 \
  $(HACL_HOME)/code/ed25519 \
  $(HACL_HOME)/code/ecdsap256sha2 \
  $(HACL_HOME)/lib \
  $(HACL_HOME)/providers/evercrypt \
  $(KREMLIN_HOME)/kremlib \
  $(HACL_HOME)/obj \
  $(EVERPARSE_HOME)/src/lowparse \
  $(OUTPUT_DIR)

# 272: top-level bindings must be total
# 247: checked file not written because some of its dependencies...
# 241: corrupt cache file AND stale cache file (argh!) we wish to make the
#      former fatal, and the latter non-fatal if it's the file we're about to
#      verify... see https://github.com/FStarLang/FStar/issues/1652
# 331: the name is being ignored
# 333: unable to open hints file
FSTAR_FLAGS=--cache_checked_modules \
  $(addprefix --include ,$(FSTAR_INCLUDES)) \
	--cache_checked_modules \
  --odir $(OUTPUT_DIR) \
  --cache_dir $(OUTPUT_DIR) \
  --use_hints \
  --record_hints \
  --already_cached 'Prims FStar LowStar Hacl Spec Lib EverCrypt Vale C Meta LowParse' \
  --warn_error -272-241-247-331-333

FSTAR=$(FSTAR_HOME)/bin/fstar.exe $(FSTAR_FLAGS) $(OTHERFLAGS)

$(OUTPUT_DIR)/%.checked: %
	$(FSTAR) $*
	touch $@

$(OUTPUT_DIR)/%.krml:
	$(FSTAR) \
	  --codegen Kremlin \
	  --cmi \
	  --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	  $(notdir $(subst .checked,,$<))

.depend:
	$(FSTAR) --dep full $(FSTAR_FILES) > .depend

depend: .depend

include .depend

verify-all: $(ALL_CHECKED_FILES)

extract-all: $(ALL_KRML_FILES)

KREMLIN_FLAGS = \
  -no-prefix 'DICE.Definitions' \
  -no-prefix 'DICE.Core' \
  -no-prefix 'DICE.Base' \
  -no-prefix 'DICE.Spec' \
  -no-prefix 'DICE.Impl' \
  -no-prefix 'RIoT.Core' \
  -no-prefix 'HWAbstraction' \
  -drop Lib.IntVector.Intrinsics \
  -fparentheses -fno-shadow -fcurly-braces \
  -library HWAbstraction \
  -bundle DICE.Definitions \
  -bundle ASN1.*,X509.* \
  -bundle LowParse.* \
  -bundle Prims,C.Failure,C,C.*,FStar.*,Hacl.*,Spec.*,Vale.*,Lib.*,LowStar.*,Meta.*[rename=Hacl_Lib] \
  -minimal \
  -fnoreturn-else \
  -add-include '"kremlin/internal/types.h"' \
  -add-include '"kremlin/lowstar_endianness.h"' \
  -add-include '<string.h>' \
  $(addprefix -I , $(FSTAR_INCLUDES)) \
  -drop WasmSupport \
  -tmpdir $(OUTPUT_DIR) \
  -verbose \
  -o riot.exe

KRML=$(KREMLIN_HOME)/krml


compile-all:
	$(KRML) \
	  $(KREMLIN_FLAGS) \
	  $(ALL_KRML_FILES) c/HWAbstraction.c

clean:
	rm -rf .depend obj dice.exe

%.fst-in %.fsti-in: 
	@echo $(addprefix --include , $(FSTAR_INCLUDES))
