dice:
	$(MAKE) -C src/dice verify-all

riot:
	$(MAKE) -C src/riot verify-all

test-riot:
	$(MAKE) -C test test-riot

test-asn1:
	$(MAKE) -C test test-asn1
