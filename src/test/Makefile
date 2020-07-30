# FSTAR_FILES=$(wildcard *.fst)
# FSTAR_FILES=$(shell find asn1/ -type f -name '*.fst')

SRC_DIR=../src

FSTAR_FILES = $(wildcard *.fst) ASN1.Test.fst

OUTPUT_DIR=obj

TEST_EXECUTABLE = asn1_test.exe

EVERPARSE_HOME ?= $(SOURCES_HOME)/everparse

FSTAR_INCLUDES=$(FSTAR_HOME)/ulib/.cache \
  $(KREMLIN_HOME)/include \
  $(KREMLIN_HOME)/kremlib/dist/generic \
  $(HACL_HOME)/specs \
  $(HACL_HOME)/specs/lemmas \
  $(HACL_HOME)/vale/specs/hardware \
  $(HACL_HOME)/vale/specs/defs \
  $(HACL_HOME)/code/meta \
  $(HACL_HOME)/code/hash \
  $(HACL_HOME)/code/hkdf \
  $(HACL_HOME)/code/hmac\
  $(HACL_HOME)/code/curve25519 \
  $(HACL_HOME)/code/ed25519 \
  $(HACL_HOME)/lib \
  $(HACL_HOME)/providers/evercrypt \
  $(KREMLIN_HOME)/kremlib \
  $(HACL_HOME)/obj \
  $(EVERPARSE_HOME)/src/lowparse \
  $(SRC_DIR) \
  $(SRC_DIR)/obj \
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
  --already_cached 'Prims FStar LowStar Hacl Spec Lib EverCrypt Vale C Meta LowParse ASN1.Base ASN1.Spec ASN1.Low X509 RIoT' \
  --warn_error -272-241-247-331-333

FSTAR_DEBUG_FLAGS=--debug $(basename $(notdir $(subst .checked,,$<))) \
	  --debug_level Extreme \

RUNEXEC_FLAGS= --no-container --memlimit 10000000000
RUNEXEC=runexec

FSTAR = $(FSTAR_HOME)/bin/fstar.exe $(FSTAR_FLAGS) $(OTHERFLAGS)

$(OUTPUT_DIR)/%.checked: %
	$(FSTAR) $*
	touch $@

$(OUTPUT_DIR)/%.krml:
	$(FSTAR) \
	  --codegen Kremlin \
	  --cmi \
    $(FSTAR_FLAGS) \
	  --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	  $(notdir $(subst .checked,,$<))

.depend: ASN1.Test.fst
	$(FSTAR) --dep full $(FSTAR_FILES) > .depend

depend: .depend

include .depend

verify-all: $(ALL_CHECKED_FILES)

extract-all: $(ALL_KRML_FILES)

KREMLIN_FLAGS = \
  -no-prefix 'ASN1.Test' \
  -no-prefix 'ASN1.Test.Helpers' \
  -no-prefix 'RIoT.Base' \
  -no-prefix 'RIoT.Spec' \
  -no-prefix 'RIoT.Impl' \
  -no-prefix 'RIoT.Core' \
  -library RIoT.Declassify \
  -library ASN1.Test.Helpers \
  -ldopt -lmbedcrypto \
  -ldopt -lmbedtls \
  -ldopt -lmbedx509 \
  -drop Lib.IntVector.Intrinsics \
  -fparentheses -fno-shadow -fcurly-braces \
  -bundle ASN1.*,X509.* \
  -bundle LowParse.* \
  -bundle Prims,C.Failure,C,C.*,FStar.*,Hacl.*,Spec.*,Vale.*,Lib.*,LowStar.*,Meta.*[rename=Hacl_Lib] \
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
  -o $(TEST_EXECUTABLE)

KRML=$(KREMLIN_HOME)/krml

compile-all:
	$(KRML) \
	  $(KREMLIN_FLAGS) \
	  $(ALL_KRML_FILES) \
    $(SRC_DIR)/c/Declassification.c \
    ASN1.Test.Helpers.c

clean:
	rm -rf .depend obj ASN1.Test.fst asn1_test.exe

ASN1.Test.fst:
	./generate_test_script.py \
    --tests ASN1.test_suites.data \
    --output ASN1.Test.fst

$(TEST_EXECUTABLE):
	OTHERFLAGS='--admit_smt_queries true' \
    $(MAKE) verify-all -j 16; \
    $(MAKE) extract-all -j 16; \
    $(MAKE) compile-all -j 16

test-all: $(TEST_EXECUTABLE)
	./$(TEST_EXECUTABLE)

%.fst-in %.fsti-in: 
	@echo $(addprefix --include , $(FSTAR_INCLUDES))
