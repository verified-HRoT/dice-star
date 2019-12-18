VHW_HOME = .
SRC_DIR = $(VHW_HOME)/src
SRC_MAIN = Minimal.DICE.fst
OUT_DIR = $(VHW_HOME)/out
OUT_NAME = Minimal.DICE

BASE_FLAGS = \
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

minimal:
	krml \
  -no-prefix \
  $(OUT_NAME) \
  $(SRC_DIR)/$(SRC_MAIN) \
  -skip-compilation \
  -tmpdir $(OUT_DIR) \
  -I $(SRC_DIR) \
  $(addprefix -I , $(INCLUDE_PATHS)) \
  -warn-error +11

compile:
	krml \
  $(SRC_DIR)/$(SRC_MAIN) \
  -cc clang \
  $(BASE_FLAGS) \
  -drop WasmSupport \
  -tmpdir $(OUT_DIR) \
  -I $(SRC_DIR) \
  -add-include '"kremlin/internal/compat.h"' \
  $(addprefix -I , $(INCLUDE_PATHS)) \
  -o dice.exe

test:
	krml \
  -no-prefix \
  Test \
  $(SRC_DIR)/Test.fst \
  -drop WasmSupport \
  -tmpdir $(OUT_DIR) \
  -I $(SRC_DIR) \
  $(addprefix -I , $(INCLUDE_PATHS)) \
  -warn-error +11 \
  -o test.exe


%.fst-in %.fsti-in: 
	@echo $(addprefix --include , $(INCLUDE_PATHS))
