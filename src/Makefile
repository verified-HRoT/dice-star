OUTPUT_DIR=./obj

DIST_DIR=../dist

DICE_ENGINE_DIST_DIR=$(DIST_DIR)/dice_engine
L0_DIST_DIR=$(DIST_DIR)/l0

DICE_ENGINE_DIST_LIB_DIR=$(DICE_ENGINE_DIST_DIR)/internal
L0_DIST_LIB_DIR=$(L0_DIST_DIR)/internal

HACL_LIB=Hacl_Lib

dist:
	$(MAKE) -C dice_engine verify-all
	$(MAKE) -C dice_engine extract-all
	$(MAKE) -C dice_engine compile-all

	$(MAKE) -C l0 verify-all
	$(MAKE) -C l0 extract-all
	$(MAKE) -C l0 compile-all

	$(MAKE) -C test verify-all
	$(MAKE) -C test extract-all
	$(MAKE) -C test compile-all

clean:
	$(MAKE) -C dice_engine clean
	$(MAKE) -C l0 clean
	$(MAKE) -C test clean
