OUTPUT_DIR=obj

DIST_DIR=../dist

DICE_ENGINE_DIST_DIR=$(DIST_DIR)/dice_engine
L0_DIST_DIR=$(DIST_DIR)/l0

DICE_ENGINE_DIST_LIB_DIR=$(DICE_ENGINE_DIST_DIR)/lib
L0_DIST_LIB_DIR=$(L0_DIST_DIR)/lib

HACL_LIB=Hacl_Lib

dist:
	$(MAKE) -C dice_engine verify-all
	$(MAKE) -C dice_engine extract-all
	$(MAKE) -C dice_engine compile-all
	mv $(OUTPUT_DIR)/$(HACL_LIB).c $(DICE_ENGINE_DIST_LIB_DIR)
	mv $(OUTPUT_DIR)/$(HACL_LIB).h $(DICE_ENGINE_DIST_LIB_DIR)
	mv $(OUTPUT_DIR)/EverCrypt_Helpers.h $(DICE_ENGINE_DIST_LIB_DIR)
	mv $(OUTPUT_DIR)/DICE_Engine_Core.c $(DICE_ENGINE_DIST_DIR)
	mv $(OUTPUT_DIR)/DICE_Engine_Core.h $(DICE_ENGINE_DIST_DIR)
	mv $(OUTPUT_DIR)/HWState.h $(DICE_ENGINE_DIST_DIR)
	mv $(OUTPUT_DIR)/HWAbstraction.h $(DICE_ENGINE_DIST_DIR)

	$(MAKE) -C test verify-all
	$(MAKE) -C test extract-all
	$(MAKE) -C test compile-all
	mv $(OUTPUT_DIR)/$(HACL_LIB).c $(L0_DIST_LIB_DIR)
	mv $(OUTPUT_DIR)/$(HACL_LIB).h $(L0_DIST_LIB_DIR)
	mv $(OUTPUT_DIR)/EverCrypt_Helpers.h $(L0_DIST_LIB_DIR)
	mv $(OUTPUT_DIR)/ASN1*.h $(L0_DIST_DIR)
	mv $(OUTPUT_DIR)/L0_X509*.h $(L0_DIST_DIR)
	mv $(OUTPUT_DIR)/L0_Core.h $(L0_DIST_DIR)
	mv $(OUTPUT_DIR)/L0_Impl*.h $(L0_DIST_DIR)
	mv $(OUTPUT_DIR)/ASN1*.c $(L0_DIST_DIR)
	mv $(OUTPUT_DIR)/L0_X509*.c $(L0_DIST_DIR)
	mv $(OUTPUT_DIR)/L0_Core.c $(L0_DIST_DIR)
	mv $(OUTPUT_DIR)/L0_Impl*.c $(L0_DIST_DIR)
	mv $(OUTPUT_DIR)/L0_Declassify.h $(L0_DIST_DIR)
	mv $(OUTPUT_DIR)/L0_Helpers.h $(L0_DIST_DIR)

clean:
	$(MAKE) -C dice_engine clean
	$(MAKE) -C test clean
