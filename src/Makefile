VHW_HOME = .
SRC_DIR = $(VHW_HOME)/src
SRC_MAIN = Minimal.DICE.fst
OUT_DIR = $(VHW_HOME)/out
OUT_NAME = Minimal.DICE

INCLUDE_PATHS = \
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

%.fst-in %.fsti-in: 
	@echo $(addprefix --include , $(INCLUDE_PATHS))
