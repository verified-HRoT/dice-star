include ../Makefile.include
include ../Makefile.common
include ../Makefile.local

clean-test:
	rm -f .depend ASN1.Test.fst RIoT.Test.fst *.exe *.key *.hex *.pem

test-asn1: clean-test
	$(TEST_DIR)/generate_test_script.py --target asn1
	OTHERFLAGS='--admit_smt_queries true' make verify-all -j32; make extract-all -j32; make compile-all -j32
	./test.exe

test-riot: clean-test
	$(TEST_DIR)/generate_test_script.py --target riot
	OTHERFLAGS='--admit_smt_queries true' make verify-all -j32; make extract-all -j32; make compile-all -j32
	./test.exe
	@cat AliasKeyCrt.hex | xxd -r -p | openssl x509 -inform DER -out AliasKeyCrt.pem;
	openssl x509 -in AliasKeyCrt.pem -text -noout
