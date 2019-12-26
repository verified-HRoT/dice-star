FSTAR_FILES=$(wildcard *.fst)

OUTPUT_DIR=obj

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
  $(OUTPUT_DIR)

FSTAR_FLAGS=--cache_checked_modules \
  $(addprefix --include ,$(FSTAR_INCLUDES)) \
  --odir $(OUTPUT_DIR) \
  --cache_dir $(OUTPUT_DIR) \
  --already_cached 'Prims FStar LowStar Hacl Spec Lib EverCrypt Vale C Meta'

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

#AR: TODO: Figure what's up with error 9

KREMLIN_FLAGS = \
  -no-prefix 'DICE.Definitions' \
  -no-prefix 'DICE.Core' \
  -no-prefix 'HWAbstraction' \
  -drop Lib.IntVector.Intrinsics \
  -fparentheses -fno-shadow -fcurly-braces \
  -library HWAbstraction \
  -bundle Prims,C.Failure,C,C.String,C.Loops,Spec.Loops,C.Endianness,FStar.*,Hacl.*,Spec.*,Vale.*,Lib.*,LowStar.*,Meta.*[rename=Hacl_Lib] \
  -minimal \
  -fnoreturn-else \
  -add-include '"kremlin/internal/types.h"' \
  -add-include '"kremlin/lowstar_endianness.h"' \
  -add-include '<string.h>' \
  $(addprefix -I , $(FSTAR_INCLUDES)) \
  -drop WasmSupport \
  -skip-linking \
  -warn-error -9 \
  -tmpdir $(OUTPUT_DIR)

KRML=$(KREMLIN_HOME)/krml


compile-all:
	$(KRML) \
	  $(KREMLIN_FLAGS) \
	  $(ALL_KRML_FILES)

clean:
	rm -rf .depend obj
