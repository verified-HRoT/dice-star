FSTAR_FILES=$(wildcard *.fst)

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
  $(HACL_HOME)/obj

FSTAR_FLAGS=--cache_checked_modules \
  $(addprefix --include ,$(FSTAR_INCLUDES)) \
  --already_cached 'Prims FStar LowStar Hacl Spec Lib EverCrypt Vale C Meta'

FSTAR=$(FSTAR_HOME)/bin/fstar.exe $(FSTAR_FLAGS) $(OTHERFLAGS)

%.checked: %
	$(FSTAR) $*
	touch $@

%.krml:
	$(FSTAR) \
	  --codegen Kremlin \
	  --cmi \
	  --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	  $(notdir $(subst .checked,,$<))

.depend:
	$(FSTAR) --dep full $(FSTAR_FILES) --extract '-* +DICE +HWAbstraction' > .depend

depend: .depend

include .depend

verify-all: $(ALL_CHECKED_FILES)

extract-all: $(ALL_KRML_FILES)

KREMLIN_FLAGS = \
  -no-prefix 'DICE.Definitions' \
  -no-prefix 'DICE.Core' \
  -no-prefix 'HWAbstraction' \
  -bundle Hacl.Spec.*,Spec.*[rename=Hacl_Spec] \
  -bundle Lib.*[rename=Hacl_Lib] \
  -drop Lib.IntVector.Intrinsics \
  -fparentheses -fno-shadow -fcurly-braces \
  -bundle LowStar.* \
  -bundle Prims,C.Failure,C,C.String,C.Loops,Spec.Loops,C.Endianness,FStar.*[rename=Hacl_Kremlib] \
  -bundle 'Meta.*' \
  -bundle 'Vale.*' \
  -minimal \
  -fnoreturn-else \
  -add-include '"kremlin/internal/types.h"' \
  -add-include '"kremlin/lowstar_endianness.h"' \
  -add-include '<string.h>' \
  $(addprefix -I , $(FSTAR_INCLUDES)) \
  -drop WasmSupport \
  -skip-compilation \
  -warn-error -9


KRML=$(KREMLIN_HOME)/krml


compile-all:
	$(KRML) \
	  $(KREMLIN_FLAGS) \
	  $(ALL_KRML_FILES)

clean:
	rm -f .depend *.checked *.krml


# VHW_HOME = .
# SRC_DIR = $(VHW_HOME)/src
# SRC_MAIN = DICE.Core.fst
# OUT_DIR = $(VHW_HOME)/out
# OUT_NAME = Dice.Core

# HACL_BASE_FLAGS = \
#   -no-prefix 'DICE.Definitions' \
#   -no-prefix 'DICE.Core' \
#   -no-prefix 'HWAbstraction' \
#   -bundle Hacl.Spec.*,Spec.*[rename=Hacl_Spec] \
#   -bundle Lib.*[rename=Hacl_Lib] \
#   -drop Lib.IntVector.Intrinsics \
#   -fparentheses -fno-shadow -fcurly-braces \
#   -bundle LowStar.* \
#   -bundle Prims,C.Failure,C,C.String,C.Loops,Spec.Loops,C.Endianness,FStar.*[rename=Hacl_Kremlib] \
#   -bundle 'Meta.*' \
#   -minimal \
#   -fnoreturn-else \
#   -add-include '"kremlin/internal/types.h"' \
#   -add-include '"kremlin/lowstar_endianness.h"' \
#   -add-include '<string.h>'

# INCLUDE_PATHS = \
#   $(KREMLIN_HOME)/include \
#   $(KREMLIN_HOME)/kremlib/dist/generic \
#   $(HACL_HOME)/specs \
#   $(HACL_HOME)/specs/lemmas \
#   $(HACL_HOME)/code/hash \
#   $(HACL_HOME)/code/hkdf \
#   $(HACL_HOME)/code/hmac\
#   $(HACL_HOME)/code/curve25519 \
#   $(HACL_HOME)/code/ed25519 \
#   $(HACL_HOME)/lib \
#   $(HACL_HOME)/providers/evercrypt \
#   $(KREMLIN_HOME)/kremlib \
#   $(HACL_HOME)/obj


# COMPILE_COMMAND = \
#   $(SRC_DIR)/$(SRC_MAIN) \
#   $(HACL_BASE_FLAGS) \
#   -drop WasmSupport \
#   -tmpdir $(OUT_DIR) \
#   -I $(SRC_DIR) \
#   -add-include '"kremlin/internal/compat.h"' \
#   $(addprefix -I , $(INCLUDE_PATHS)) \
#   -o $(OUT_DIR)/dice.exe

# extract:
# 	krml \
#   -skip-compilation \
#   $(COMPILE_COMMAND)

# compile:
# 	krml \
#   $(COMPILE_COMMAND)

# %.fst-in %.fsti-in: 
# 	@echo $(addprefix --include , $(INCLUDE_PATHS))
