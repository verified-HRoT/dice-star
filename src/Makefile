VHW_HOME = .
SRC_DIR = $(VHW_HOME)/src
SRC_MAIN = Minimal.DICE.fst
OUT_DIR = $(VHW_HOME)/out
OUT_NAME = Minimal.DICE

HACL_BASE_FLAGS = \
  -no-prefix 'Hacl.Frodo.Random' \
  -bundle Hacl.Spec.*,Spec.*[rename=Hacl_Spec] \
  -bundle Lib.*[rename=Hacl_Lib] \
  -drop Lib.IntVector.Intrinsics \
  -fparentheses -fno-shadow -fcurly-braces \
  -bundle LowStar.* \
  -bundle Prims,C.Failure,C,C.String,C.Loops,Spec.Loops,C.Endianness,FStar.*[rename=Hacl_Kremlib] \
  -bundle 'Meta.*' \
  -minimal \
  -add-include '"kremlin/internal/types.h"' \
  -add-include '"kremlin/lowstar_endianness.h"' \
  -add-include '<string.h>'

INCLUDE_PATHS = \
  $(KREMLIN_HOME)/include \
  $(KREMLIN_HOME)/kremlib/dist/generic \
  $(HACL_HOME)/specs \
  $(HACL_HOME)/specs/lemmas \
  $(HACL_HOME)/code/hash \
  $(HACL_HOME)/code/hkdf \
  $(HACL_HOME)/code/hmac\
  $(HACL_HOME)/code/curve25519 \
  $(HACL_HOME)/code/ed25519 \
  $(HACL_HOME)/lib \
  $(HACL_HOME)/providers/evercrypt \
  $(KREMLIN_HOME)/kremlib

COMPILE_COMMAND = \
  $(SRC_DIR)/$(SRC_MAIN) \
  $(HACL_BASE_FLAGS) \
  -drop WasmSupport \
  -tmpdir $(OUT_DIR) \
  -I $(SRC_DIR) \
  -add-include '"kremlin/internal/compat.h"' \
  $(addprefix -I , $(INCLUDE_PATHS)) \
  -o $(OUT_DIR)/dice.exe

extract:
	krml \
  -skip-compilation \
  $(COMPILE_COMMAND)

compile:
	krml \
  $(COMPILE_COMMAND)

%.fst-in %.fsti-in: 
	@echo $(addprefix --include , $(INCLUDE_PATHS))
