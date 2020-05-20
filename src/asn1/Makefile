FSTAR_FILES=$(wildcard *.fst)

OUTPUT_DIR=obj

EVERPARSE_HOME ?= $(SOURCES_HOME)/everparse

FSTAR_INCLUDES=$(FSTAR_HOME)/ulib/.cache \
  $(KREMLIN_HOME)/include \
  $(KREMLIN_HOME)/kremlib/dist/generic \
  $(KREMLIN_HOME)/kremlib \
  $(HACL_HOME)/lib \
  $(HACL_HOME)/obj \
  $(EVERPARSE_HOME)/src/lowparse \
  $(OUTPUT_DIR)

FSTAR_FLAGS=--cache_checked_modules \
  $(addprefix --include ,$(FSTAR_INCLUDES)) \
	--cache_checked_modules \
  --odir $(OUTPUT_DIR) \
  --cache_dir $(OUTPUT_DIR) \
  --use_hints \
  --record_hints \
  --already_cached 'Prims FStar LowStar C LowParse Spec Lib'

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

# $(ALL_CHECKED_FILES): %.checked:
# 	$(FSTAR_EXE) $(FSTAR_OPTIONS) $(OTHERFLAGS) $<
# 	touch $@

extract-all: $(ALL_KRML_FILES)

KREMLIN_FLAGS = \
  -no-prefix 'ASN1.Test' \
  -no-prefix 'ASN1.Test.Helpers' \
  -ldopt -lmbedcrypto \
  -ldopt -lmbedtls \
  -ldopt -lmbedx509 \
  -fparentheses -fno-shadow -fcurly-braces \
  -bundle Prims,C.Failure,C,C.*,FStar.*,LowStar.*,Lib.*,LowParse.* \
  -minimal \
  -fnoreturn-else \
  -add-include '"kremlin/internal/types.h"' \
  -add-include '"kremlin/lowstar_endianness.h"' \
  -add-include '"LowStar_Printf.h"' \
  -add-include '<string.h>' \
  $(addprefix -I , $(FSTAR_INCLUDES)) \
  -drop WasmSupport \
  -tmpdir $(OUTPUT_DIR) \
  -verbose \
  -o asn1_test.exe

KRML=$(KREMLIN_HOME)/krml


compile-all:
	$(KRML) \
	  $(KREMLIN_FLAGS) \
	  $(ALL_KRML_FILES) \
		ASN1.Test.Helpers.c

clean:
	rm -rf .depend obj asn1_test.exe

%.fst-in %.fsti-in: 
	@echo $(addprefix --include , $(FSTAR_INCLUDES))
