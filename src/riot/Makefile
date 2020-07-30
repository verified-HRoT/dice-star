include ../Makefile.include
include ../Makefile.common
include ../Makefile.local

format-all:
	openssl base64 -in AliasKeyCrt.hex -out AliasKeyCrt.pem;
	sed -i '1s/^/-----BEGIN CERTIFICATE-----\n/' AliasKeyCrt.pem;
	echo "-----END CERTIFICATE-----" >> AliasKeyCrt.pem;
	openssl base64 -in AliasKeyPrivateKey.hex -out AliasKeyPrivateKey.key;
	sed -i '1s/^/-----BEGIN EC PRIVATE KEY-----\n/' AliasKeyPrivateKey.key;
	echo "-----END EC PRIVATE KEY-----" >> AliasKeyPrivateKey.key;
	openssl base64 -in AliasKeyPublicKey.hex -out AliasKeyPublicKey.key;
	sed -i '1s/^/-----BEGIN PUBLIC KEY-----\n/' AliasKeyPublicKey.key;
	echo "-----END PUBLIC KEY-----" >> AliasKeyPublicKey.key;

check-all:
	echo "Checking AliasKeyPrivateKey.key";
	openssl ec -in AliasKeyPrivateKey.key -check;
	echo "Checking AliasKeyCrt.pem";
	openssl x509 -in AliasKeyCrt.pem -text -noout