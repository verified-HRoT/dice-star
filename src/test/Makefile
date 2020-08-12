include ../Makefile.include
include ../Makefile.common
include ../Makefile.local

clean-test:
	rm -f .depend ASN1.Test.fst RIoT.Test.fst *.exe *.key *.hex *.pem *.csr

test-asn1: clean-test
	$(TEST_DIR)/generate_test_script.py --target asn1
	make verify-all -j32; make extract-all -j32; make compile-all -j32
	@./test.exe

test-riot: clean-test
	$(TEST_DIR)/generate_test_script.py --target riot
	make verify-all -j32; make extract-all -j32; make compile-all -j32
	@./test.exe
	@cat DeviceIDCSR.hex | xxd -r -p | openssl req -inform DER -out DeviceIDCSR.csr
	@cat AliasKeyCrt.hex | xxd -r -p | openssl x509 -inform DER -out AliasKeyCrt.pem
	@if openssl x509 -in AliasKeyCrt.pem -text -noout; then \
      printf "[RIoT] Passed AliasKey Crt test!👍\n"; \
    else \
      printf "[RIoT] Failed AliasKey Crt test!🔥\n"; \
    fi && \
	if openssl req -in DeviceIDCSR.csr -text -noout; then \
      printf "[RIoT] Passed DeviceID CSR test!👍\n"; \
    else \
      printf "[RIoT] Failed DeviceID CSR test!🔥\n"; \
    fi
