include ../Makefile.include
include ../Makefile.common
include ../Makefile.local

format-all:
	@cat AliasKeyCrt.hex | xxd -r -p | openssl x509 -inform DER -out AliasKeyCrt.pem;

check-all:
	openssl x509 -in AliasKeyCrt.pem -text -noout