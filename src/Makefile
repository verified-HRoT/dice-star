VHW_HOME = .
SRC_DIR = $(VHW_HOME)/src
SRC_MAIN = Minimal.DICE.fst
OUT_DIR = $(VHW_HOME)/out
OUT_NAME = Minimal.DICE

minimal:
	krml \
  -no-prefix \
  $(OUT_NAME) \
  $(SRC_DIR)/$(SRC_MAIN) \
  -skip-compilation \
  -tmpdir $(OUT_DIR) \
  -I $(SRC_DIR) \
  -I $(HACL_HOME)/specs \
  -I $(HACL_HOME)/specs/lemmas \
  -I $(HACL_HOME)/code/hash \
  -I $(HACL_HOME)/code/hkdf \
  -I $(HACL_HOME)/code/hmac \
  -I $(HACL_HOME)/code/curve25519 \
  -I $(HACL_HOME)/code/ed25519 \
  -I $(HACL_HOME)/lib \
  -I $(HACL_HOME)/providers/evercrypt \
  -warn-error +11
