module ASN1.Spec.Value.OID

open ASN1.Spec.Base

open ASN1.Base
open ASN1.Spec.Tag
open ASN1.Spec.Length
open LowParse.Spec.SeqBytes.Base

open FStar.Integers

unfold noextract
let ( @ ) = List.Tot.Base.append

(* Top level OID tuples
  =====================
#define MBEDTLS_OID_ISO_MEMBER_BODIES           "\x2a"          /* {iso(1) member-body(2)} */
#define MBEDTLS_OID_ISO_IDENTIFIED_ORG          "\x2b"          /* {iso(1) identified-organization(3)} */
#define MBEDTLS_OID_ISO_CCITT_DS                "\x55"          /* {joint-iso-ccitt(2) ds(5)} */
#define MBEDTLS_OID_ISO_ITU_COUNTRY             "\x60"          /* {joint-iso-itu-t(2) country(16)} */
*)
noextract let oid_head_ISO_MEMBER_BODIES  = [0x2Auy]
noextract let oid_head_ISO_IDENTIFIED_ORG = [0x2Buy]
noextract let oid_head_ISO_CCITT_DS       = [0x55uy]
noextract let oid_head_ISO_ITU_COUNTRY    = [0x60uy]

(* ISO Member bodies OID parts
  ============================
#define MBEDTLS_OID_COUNTRY_US                  "\x86\x48"      /* {us(840)} */
#define MBEDTLS_OID_ORG_RSA_DATA_SECURITY       "\x86\xf7\x0d"  /* {rsadsi(113549)} */
#define MBEDTLS_OID_RSA_COMPANY                 MBEDTLS_OID_ISO_MEMBER_BODIES MBEDTLS_OID_COUNTRY_US \
                                        MBEDTLS_OID_ORG_RSA_DATA_SECURITY /* {iso(1) member-body(2) us(840) rsadsi(113549)} */
#define MBEDTLS_OID_ORG_ANSI_X9_62              "\xce\x3d" /* ansi-X9-62(10045) */
#define MBEDTLS_OID_ANSI_X9_62                  MBEDTLS_OID_ISO_MEMBER_BODIES MBEDTLS_OID_COUNTRY_US \
                                        MBEDTLS_OID_ORG_ANSI_X9_62
*)
noextract let oid_node_COUNTRY_US     = [0x86uy; 0x48uy]
noextract let oid_node_ORG_ANSI_X9_62 = [0xceuy; 0x3duy]
noextract let oid_ANSI_X9_62          = oid_head_ISO_MEMBER_BODIES @ oid_node_ORG_ANSI_X9_62

(* ISO ITU OID parts
  ==================
#define MBEDTLS_OID_ORGANIZATION                "\x01"          /* {organization(1)} */
#define MBEDTLS_OID_ISO_ITU_US_ORG              MBEDTLS_OID_ISO_ITU_COUNTRY MBEDTLS_OID_COUNTRY_US MBEDTLS_OID_ORGANIZATION /* {joint-iso-itu-t(2) country(16) us(840) organization(1)} */

#define MBEDTLS_OID_ORG_GOV                     "\x65"          /* {gov(101)} */
#define MBEDTLS_OID_GOV                         MBEDTLS_OID_ISO_ITU_US_ORG MBEDTLS_OID_ORG_GOV /* {joint-iso-itu-t(2) country(16) us(840) organization(1) gov(101)} */

#define MBEDTLS_OID_ORG_NETSCAPE                "\x86\xF8\x42"  /* {netscape(113730)} */
#define MBEDTLS_OID_NETSCAPE                    MBEDTLS_OID_ISO_ITU_US_ORG MBEDTLS_OID_ORG_NETSCAPE /* Netscape OID {joint-iso-itu-t(2) country(16) us(840) organization(1) netscape(113730)} */
*)
noextract let oid_node_ORGANIZATION = [0x01uy]
noextract let oid_ISO_ITU_US_ORG    = oid_head_ISO_ITU_COUNTRY @ oid_node_COUNTRY_US @ oid_node_ORGANIZATION

noextract let oid_node_ISO_ORG_GOV  = [0x65uy]
noextract let oid_GOV               = oid_ISO_ITU_US_ORG @ oid_node_ISO_ORG_GOV

(* ISO arc for standard certificate and CRL extensions
  =====================================================
#define MBEDTLS_OID_ID_CE                       MBEDTLS_OID_ISO_CCITT_DS "\x1D" /**< id-ce OBJECT IDENTIFIER  ::=  {joint-iso-ccitt(2) ds(5) 29} */

#define MBEDTLS_OID_NIST_ALG                    MBEDTLS_OID_GOV "\x03\x04" /** { joint-iso-itu-t(2) country(16) us(840) organization(1) gov(101) csor(3) nistAlgorithm(4) */
*)
noextract let oid_ID_CE    = oid_head_ISO_CCITT_DS @ [0x1Duy]

noextract let oid_NIST_ALG = oid_GOV @ [0x03uy; 0x04uy]

(* Private Internet Extensions
   { iso(1) identified-organization(3) dod(6) internet(1)
                        security(5) mechanisms(5) pkix(7) }
  =========================================================
#define MBEDTLS_OID_INTERNET                    MBEDTLS_OID_ISO_IDENTIFIED_ORG MBEDTLS_OID_ORG_DOD "\x01"
#define MBEDTLS_OID_PKIX                        MBEDTLS_OID_INTERNET "\x05\x05\x07"
*)
noextract let oid_INTERNET = oid_head_ISO_IDENTIFIED_ORG @ [0x01uy]
noextract let oid_PKIX     = oid_INTERNET @ [0x05uy; 0x05uy; 0x07uy]

(* Arc for standard naming attributes
  ===================================
#define MBEDTLS_OID_AT                          MBEDTLS_OID_ISO_CCITT_DS "\x04" /**< id-at OBJECT IDENTIFIER ::= {joint-iso-ccitt(2) ds(5) 4} */
#define MBEDTLS_OID_AT_CN                       MBEDTLS_OID_AT "\x03" /**< id-at-commonName AttributeType:= {id-at 3} */
#define MBEDTLS_OID_AT_SUR_NAME                 MBEDTLS_OID_AT "\x04" /**< id-at-surName AttributeType:= {id-at 4} */
#define MBEDTLS_OID_AT_SERIAL_NUMBER            MBEDTLS_OID_AT "\x05" /**< id-at-serialNumber AttributeType:= {id-at 5} */
#define MBEDTLS_OID_AT_COUNTRY                  MBEDTLS_OID_AT "\x06" /**< id-at-countryName AttributeType:= {id-at 6} */
#define MBEDTLS_OID_AT_LOCALITY                 MBEDTLS_OID_AT "\x07" /**< id-at-locality AttributeType:= {id-at 7} */
#define MBEDTLS_OID_AT_STATE                    MBEDTLS_OID_AT "\x08" /**< id-at-state AttributeType:= {id-at 8} */
#define MBEDTLS_OID_AT_ORGANIZATION             MBEDTLS_OID_AT "\x0A" /**< id-at-organizationName AttributeType:= {id-at 10} */
#define MBEDTLS_OID_AT_ORG_UNIT                 MBEDTLS_OID_AT "\x0B" /**< id-at-organizationalUnitName AttributeType:= {id-at 11} */
#define MBEDTLS_OID_AT_TITLE                    MBEDTLS_OID_AT "\x0C" /**< id-at-title AttributeType:= {id-at 12} */
#define MBEDTLS_OID_AT_POSTAL_ADDRESS           MBEDTLS_OID_AT "\x10" /**< id-at-postalAddress AttributeType:= {id-at 16} */
#define MBEDTLS_OID_AT_POSTAL_CODE              MBEDTLS_OID_AT "\x11" /**< id-at-postalCode AttributeType:= {id-at 17} */
#define MBEDTLS_OID_AT_GIVEN_NAME               MBEDTLS_OID_AT "\x2A" /**< id-at-givenName AttributeType:= {id-at 42} */
#define MBEDTLS_OID_AT_INITIALS                 MBEDTLS_OID_AT "\x2B" /**< id-at-initials AttributeType:= {id-at 43} */
#define MBEDTLS_OID_AT_GENERATION_QUALIFIER     MBEDTLS_OID_AT "\x2C" /**< id-at-generationQualifier AttributeType:= {id-at 44} */
#define MBEDTLS_OID_AT_UNIQUE_IDENTIFIER        MBEDTLS_OID_AT "\x2D" /**< id-at-uniqueIdentifier AttributType:= {id-at 45} */
#define MBEDTLS_OID_AT_DN_QUALIFIER             MBEDTLS_OID_AT "\x2E" /**< id-at-dnQualifier AttributeType:= {id-at 46} */
#define MBEDTLS_OID_AT_PSEUDONYM                MBEDTLS_OID_AT "\x41" /**< id-at-pseudonym AttributeType:= {id-at 65} */

#define MBEDTLS_OID_DOMAIN_COMPONENT            "\x09\x92\x26\x89\x93\xF2\x2C\x64\x01\x19" /** id-domainComponent AttributeType:= {itu-t(0) data(9) pss(2342) ucl(19200300) pilot(100) pilotAttributeType(1) domainComponent(25)} */
*)
noextract let oid_AT                      = oid_head_ISO_CCITT_DS @ [0x04uy] (* id-at OBJECT IDENTIFIER ::= {joint-iso-ccitt(2) ds(5) 4} *)
noextract let oid_AT_CN                   = oid_AT @ [0x03uy]           (* id-at-commonName AttributeType:= {id-at 3} *)
// noextract let oid_AT_SUR_NAME             = oid_AT @ [0x04uy]           (* id-at-surName AttributeType:= {id-at 4} *)
// noextract let oid_AT_SERIAL_NUMBER        = oid_AT @ [0x05uy]           (* id-at-serialNumber AttributeType:= {id-at 5} *)
noextract let oid_AT_COUNTRY              = oid_AT @ [0x06uy]           (* id-at-countryName AttributeType:= {id-at 6} *)
// noextract let oid_AT_LOCALITY             = oid_AT @ [0x07uy]           (* id-at-locality AttributeType:= {id-at 7} *)
// noextract let oid_AT_STATE                = oid_AT @ [0x08uy]           (* id-at-state AttributeType:= {id-at 8} *)
noextract let oid_AT_ORGANIZATION         = oid_AT @ [0x0Auy]           (* id-at-organizationName AttributeType:= {id-at 10} *)
// noextract let oid_AT_ORG_UNIT             = oid_AT @ [0x0Buy]           (* id-at-organizationalUnitName AttributeType:= {id-at 11} *)
// noextract let oid_AT_TITLE                = oid_AT @ [0x0Cuy]           (* id-at-title AttributeType:= {id-at 12} *)
// noextract let oid_AT_POSTAL_ADDRESS       = oid_AT @ [0x10uy]           (* id-at-postalAddress AttributeType:= {id-at 16} *)
// noextract let oid_AT_POSTAL_CODE          = oid_AT @ [0x11uy]           (* id-at-postalCode AttributeType:= {id-at 17} *)
// noextract let oid_AT_GIVEN_NAME           = oid_AT @ [0x2Auy]           (* id-at-givenName AttributeType:= {id-at 42} *)
// noextract let oid_AT_INITIALS             = oid_AT @ [0x2Buy]           (* id-at-initials AttributeType:= {id-at 43} *)
// noextract let oid_AT_GENERATION_QUALIFIER = oid_AT @ [0x2Cuy]           (* id-at-generationQualifier AttributeType:= {id-at 44} *)
// noextract let oid_AT_UNIQUE_IDENTIFIER    = oid_AT @ [0x2Duy]           (* id-at-uniqueIdentifier AttributType:= {id-at 45} *)
// noextract let oid_AT_DN_QUALIFIER         = oid_AT @ [0x2Euy]           (* id-at-dnQualifier AttributeType:= {id-at 46} *)
// noextract let oid_AT_PSEUDONYM            = oid_AT @ [0x41uy]           (* id-at-pseudonym AttributeType:= {id-at 65} *)

noextract let oid_DOMAIN_COMPONENT        =    [0x09uy; 0x92uy; 0x26uy; 0x89uy; 0x93uy; 0xF2uy; 0x2Cuy; 0x64uy; 0x01uy; 0x19uy] (* id-domainComponent AttributeType:= {itu-t(0) data(9) pss(2342) ucl(19200300) pilot(100) pilotAttributeType(1) domainComponent(25)} *)


(* OIDs for standard certificate extensions
  =========================================
#define MBEDTLS_OID_AUTHORITY_KEY_IDENTIFIER    MBEDTLS_OID_ID_CE "\x23" /**< id-ce-authorityKeyIdentifier OBJECT IDENTIFIER ::=  { id-ce 35 } */
#define MBEDTLS_OID_SUBJECT_KEY_IDENTIFIER      MBEDTLS_OID_ID_CE "\x0E" /**< id-ce-subjectKeyIdentifier OBJECT IDENTIFIER ::=  { id-ce 14 } */
#define MBEDTLS_OID_KEY_USAGE                   MBEDTLS_OID_ID_CE "\x0F" /**< id-ce-keyUsage OBJECT IDENTIFIER ::=  { id-ce 15 } */
#define MBEDTLS_OID_CERTIFICATE_POLICIES        MBEDTLS_OID_ID_CE "\x20" /**< id-ce-certificatePolicies OBJECT IDENTIFIER ::=  { id-ce 32 } */
#define MBEDTLS_OID_POLICY_MAPPINGS             MBEDTLS_OID_ID_CE "\x21" /**< id-ce-policyMappings OBJECT IDENTIFIER ::=  { id-ce 33 } */
#define MBEDTLS_OID_SUBJECT_ALT_NAME            MBEDTLS_OID_ID_CE "\x11" /**< id-ce-subjectAltName OBJECT IDENTIFIER ::=  { id-ce 17 } */
#define MBEDTLS_OID_ISSUER_ALT_NAME             MBEDTLS_OID_ID_CE "\x12" /**< id-ce-issuerAltName OBJECT IDENTIFIER ::=  { id-ce 18 } */
#define MBEDTLS_OID_SUBJECT_DIRECTORY_ATTRS     MBEDTLS_OID_ID_CE "\x09" /**< id-ce-subjectDirectoryAttributes OBJECT IDENTIFIER ::=  { id-ce 9 } */
#define MBEDTLS_OID_BASIC_CONSTRAINTS           MBEDTLS_OID_ID_CE "\x13" /**< id-ce-basicConstraints OBJECT IDENTIFIER ::=  { id-ce 19 } */
#define MBEDTLS_OID_NAME_CONSTRAINTS            MBEDTLS_OID_ID_CE "\x1E" /**< id-ce-nameConstraints OBJECT IDENTIFIER ::=  { id-ce 30 } */
#define MBEDTLS_OID_POLICY_CONSTRAINTS          MBEDTLS_OID_ID_CE "\x24" /**< id-ce-policyConstraints OBJECT IDENTIFIER ::=  { id-ce 36 } */
#define MBEDTLS_OID_EXTENDED_KEY_USAGE          MBEDTLS_OID_ID_CE "\x25" /**< id-ce-extKeyUsage OBJECT IDENTIFIER ::= { id-ce 37 } */
#define MBEDTLS_OID_CRL_DISTRIBUTION_POINTS     MBEDTLS_OID_ID_CE "\x1F" /**< id-ce-cRLDistributionPoints OBJECT IDENTIFIER ::=  { id-ce 31 } */
#define MBEDTLS_OID_INIHIBIT_ANYPOLICY          MBEDTLS_OID_ID_CE "\x36" /**< id-ce-inhibitAnyPolicy OBJECT IDENTIFIER ::=  { id-ce 54 } */
#define MBEDTLS_OID_FRESHEST_CRL                MBEDTLS_OID_ID_CE "\x2E" /**< id-ce-freshestCRL OBJECT IDENTIFIER ::=  { id-ce 46 } */
*)
noextract let oid_AUTHORITY_KEY_IDENTIFIER = oid_ID_CE @ [0x23uy]
noextract let oid_KEY_USAGE                = oid_ID_CE @ [0x0Fuy]
noextract let oid_EXTENDED_KEY_USAGE       = oid_ID_CE @ [0x25uy]
noextract let oid_BASIC_CONSTRAINTS        = oid_ID_CE @ [0x13uy]

(* X.509 v3 Extended key usage OIDs
  =================================
#define MBEDTLS_OID_ANY_EXTENDED_KEY_USAGE      MBEDTLS_OID_EXTENDED_KEY_USAGE "\x00" /**< anyExtendedKeyUsage OBJECT IDENTIFIER ::= { id-ce-extKeyUsage 0 } */

#define MBEDTLS_OID_KP                          MBEDTLS_OID_PKIX "\x03" /**< id-kp OBJECT IDENTIFIER ::= { id-pkix 3 } */
#define MBEDTLS_OID_SERVER_AUTH                 MBEDTLS_OID_KP "\x01" /**< id-kp-serverAuth OBJECT IDENTIFIER ::= { id-kp 1 } */
#define MBEDTLS_OID_CLIENT_AUTH                 MBEDTLS_OID_KP "\x02" /**< id-kp-clientAuth OBJECT IDENTIFIER ::= { id-kp 2 } */
#define MBEDTLS_OID_CODE_SIGNING                MBEDTLS_OID_KP "\x03" /**< id-kp-codeSigning OBJECT IDENTIFIER ::= { id-kp 3 } */
#define MBEDTLS_OID_EMAIL_PROTECTION            MBEDTLS_OID_KP "\x04" /**< id-kp-emailProtection OBJECT IDENTIFIER ::= { id-kp 4 } */
#define MBEDTLS_OID_TIME_STAMPING               MBEDTLS_OID_KP "\x08" /**< id-kp-timeStamping OBJECT IDENTIFIER ::= { id-kp 8 } */
#define MBEDTLS_OID_OCSP_SIGNING                MBEDTLS_OID_KP "\x09" /**< id-kp-OCSPSigning OBJECT IDENTIFIER ::= { id-kp 9 } */
*)
noextract let oid_KP          = oid_PKIX @ [0x03uy]
noextract let oid_CLIENT_AUTH = oid_KP @ [0x02uy]

(* Digest algorithms
  ==================
#define MBEDTLS_OID_DIGEST_ALG_MD2              MBEDTLS_OID_RSA_COMPANY "\x02\x02" /**< id-mbedtls_md2 OBJECT IDENTIFIER ::= { iso(1) member-body(2) us(840) rsadsi(113549) digestAlgorithm(2) 2 } */
#define MBEDTLS_OID_DIGEST_ALG_MD4              MBEDTLS_OID_RSA_COMPANY "\x02\x04" /**< id-mbedtls_md4 OBJECT IDENTIFIER ::= { iso(1) member-body(2) us(840) rsadsi(113549) digestAlgorithm(2) 4 } */
#define MBEDTLS_OID_DIGEST_ALG_MD5              MBEDTLS_OID_RSA_COMPANY "\x02\x05" /**< id-mbedtls_md5 OBJECT IDENTIFIER ::= { iso(1) member-body(2) us(840) rsadsi(113549) digestAlgorithm(2) 5 } */
#define MBEDTLS_OID_DIGEST_ALG_SHA1             MBEDTLS_OID_ISO_IDENTIFIED_ORG MBEDTLS_OID_OIW_SECSIG_SHA1 /**< id-mbedtls_sha1 OBJECT IDENTIFIER ::= { iso(1) identified-organization(3) oiw(14) secsig(3) algorithms(2) 26 } */
#define MBEDTLS_OID_DIGEST_ALG_SHA224           MBEDTLS_OID_NIST_ALG "\x02\x04" /**< id-sha224 OBJECT IDENTIFIER ::= { joint-iso-itu-t(2) country(16) us(840) organization(1) gov(101) csor(3) nistalgorithm(4) hashalgs(2) 4 } */
#define MBEDTLS_OID_DIGEST_ALG_SHA256           MBEDTLS_OID_NIST_ALG "\x02\x01" /**< id-mbedtls_sha256 OBJECT IDENTIFIER ::= { joint-iso-itu-t(2) country(16) us(840) organization(1) gov(101) csor(3) nistalgorithm(4) hashalgs(2) 1 } */

#define MBEDTLS_OID_DIGEST_ALG_SHA384           MBEDTLS_OID_NIST_ALG "\x02\x02" /**< id-sha384 OBJECT IDENTIFIER ::= { joint-iso-itu-t(2) country(16) us(840) organization(1) gov(101) csor(3) nistalgorithm(4) hashalgs(2) 2 } */

#define MBEDTLS_OID_DIGEST_ALG_SHA512           MBEDTLS_OID_NIST_ALG "\x02\x03" /**< id-mbedtls_sha512 OBJECT IDENTIFIER ::= { joint-iso-itu-t(2) country(16) us(840) organization(1) gov(101) csor(3) nistalgorithm(4) hashalgs(2) 3 } */

#define MBEDTLS_OID_DIGEST_ALG_RIPEMD160        MBEDTLS_OID_TELETRUST "\x03\x02\x01" /**< id-ripemd160 OBJECT IDENTIFIER :: { iso(1) identified-organization(3) teletrust(36) algorithm(3) hashAlgorithm(2) ripemd160(1) } */

#define MBEDTLS_OID_HMAC_SHA1                   MBEDTLS_OID_RSA_COMPANY "\x02\x07" /**< id-hmacWithSHA1 OBJECT IDENTIFIER ::= { iso(1) member-body(2) us(840) rsadsi(113549) digestAlgorithm(2) 7 } */

#define MBEDTLS_OID_HMAC_SHA224                 MBEDTLS_OID_RSA_COMPANY "\x02\x08" /**< id-hmacWithSHA224 OBJECT IDENTIFIER ::= { iso(1) member-body(2) us(840) rsadsi(113549) digestAlgorithm(2) 8 } */

#define MBEDTLS_OID_HMAC_SHA256                 MBEDTLS_OID_RSA_COMPANY "\x02\x09" /**< id-hmacWithSHA256 OBJECT IDENTIFIER ::= { iso(1) member-body(2) us(840) rsadsi(113549) digestAlgorithm(2) 9 } */

#define MBEDTLS_OID_HMAC_SHA384                 MBEDTLS_OID_RSA_COMPANY "\x02\x0A" /**< id-hmacWithSHA384 OBJECT IDENTIFIER ::= { iso(1) member-body(2) us(840) rsadsi(113549) digestAlgorithm(2) 10 } */

#define MBEDTLS_OID_HMAC_SHA512                 MBEDTLS_OID_RSA_COMPANY "\x02\x0B" /**< id-hmacWithSHA512 OBJECT IDENTIFIER ::= { iso(1) member-body(2) us(840) rsadsi(113549) digestAlgorithm(2) 11 } */
*)
noextract let oid_DIGEST_ALG_SHA224 = oid_NIST_ALG @ [0x02uy; 0x04uy]
noextract let oid_DIGEST_ALG_SHA256 = oid_NIST_ALG @ [0x02uy; 0x01uy]
noextract let oid_DIGEST_ALG_SHA384 = oid_NIST_ALG @ [0x02uy; 0x02uy]
noextract let oid_DIGEST_ALG_SHA512 = oid_NIST_ALG @ [0x02uy; 0x03uy]

(* EC key algorithms from RFC 5480
  ================================
/* id-ecPublicKey OBJECT IDENTIFIER ::= {
 *       iso(1) member-body(2) us(840) ansi-X9-62(10045) keyType(2) 1 } */
#define MBEDTLS_OID_EC_ALG_UNRESTRICTED         MBEDTLS_OID_ANSI_X9_62 "\x02\01"

/*   id-ecDH OBJECT IDENTIFIER ::= {
 *     iso(1) identified-organization(3) certicom(132)
 *     schemes(1) ecdh(12) } */
#define MBEDTLS_OID_EC_ALG_ECDH                 MBEDTLS_OID_CERTICOM "\x01\x0c"
*)

noextract let oid_EC_ALG_UNRESTRICTED = oid_ANSI_X9_62 @ [0x02uy; 0x01uy]

(* ECParameters namedCurve identifiers, from RFC 5480, RFC 5639, and SEC2
  =======================================================================
/* secp192r1 OBJECT IDENTIFIER ::= {
 *   iso(1) member-body(2) us(840) ansi-X9-62(10045) curves(3) prime(1) 1 } */
#define MBEDTLS_OID_EC_GRP_SECP192R1        MBEDTLS_OID_ANSI_X9_62 "\x03\x01\x01"

/* secp224r1 OBJECT IDENTIFIER ::= {
 *   iso(1) identified-organization(3) certicom(132) curve(0) 33 } */
#define MBEDTLS_OID_EC_GRP_SECP224R1        MBEDTLS_OID_CERTICOM "\x00\x21"

/* secp256r1 OBJECT IDENTIFIER ::= {
 *   iso(1) member-body(2) us(840) ansi-X9-62(10045) curves(3) prime(1) 7 } */
#define MBEDTLS_OID_EC_GRP_SECP256R1        MBEDTLS_OID_ANSI_X9_62 "\x03\x01\x07"

/* secp384r1 OBJECT IDENTIFIER ::= {
 *   iso(1) identified-organization(3) certicom(132) curve(0) 34 } */
#define MBEDTLS_OID_EC_GRP_SECP384R1        MBEDTLS_OID_CERTICOM "\x00\x22"

/* secp521r1 OBJECT IDENTIFIER ::= {
 *   iso(1) identified-organization(3) certicom(132) curve(0) 35 } */
#define MBEDTLS_OID_EC_GRP_SECP521R1        MBEDTLS_OID_CERTICOM "\x00\x23"

/* secp192k1 OBJECT IDENTIFIER ::= {
 *   iso(1) identified-organization(3) certicom(132) curve(0) 31 } */
#define MBEDTLS_OID_EC_GRP_SECP192K1        MBEDTLS_OID_CERTICOM "\x00\x1f"

/* secp224k1 OBJECT IDENTIFIER ::= {
 *   iso(1) identified-organization(3) certicom(132) curve(0) 32 } */
#define MBEDTLS_OID_EC_GRP_SECP224K1        MBEDTLS_OID_CERTICOM "\x00\x20"

/* secp256k1 OBJECT IDENTIFIER ::= {
 *   iso(1) identified-organization(3) certicom(132) curve(0) 10 } */
#define MBEDTLS_OID_EC_GRP_SECP256K1        MBEDTLS_OID_CERTICOM "\x00\x0a"
*)

noextract let oid_EC_GRP_SECP256R1 = oid_ANSI_X9_62 @ [0x03uy; 0x01uy; 0x07uy]

noextract let oid_EDWARDS_CURVE_ALGS = oid_head_ISO_IDENTIFIED_ORG @ [0x65uy]

noextract let oid_ED25519 = oid_EDWARDS_CURVE_ALGS @ [0x70uy]

noextract let oid_X25519 = oid_EDWARDS_CURVE_ALGS @ [0x6Euy]

(* RIoT OID
  =========
1.3.6.1.4.1.311.89.3.1
*)
(* FIXME: Check RIoT's OID *)
noextract let oid_RIOT = oid_INTERNET @ [0x04uy; 0x01uy; 0x82uy; 0x37uy; 0x59uy; 0x03uy; 0x01uy]

(* Known OIDs *)
noextract
let known_oids_as_list =
  [ oid_RIOT;
    oid_AT_CN;
    oid_AT_COUNTRY;
    oid_AT_ORGANIZATION;
    oid_CLIENT_AUTH;
    oid_AUTHORITY_KEY_IDENTIFIER;
    oid_KEY_USAGE;
    oid_EXTENDED_KEY_USAGE;
    oid_BASIC_CONSTRAINTS;
    // oid_DIGEST_ALG_SHA224;
    oid_DIGEST_ALG_SHA256;
    // oid_DIGEST_ALG_SHA384;
    // oid_DIGEST_ALG_SHA512;
    oid_EC_ALG_UNRESTRICTED;
    oid_EC_GRP_SECP256R1;
    oid_ED25519;
    oid_X25519
    ]

module T = FStar.Tactics

#push-options "--fuel 0 --ifuel 0"

(*
 * This proof goes through as is,
 * the normalize_term marker in the postcondition unfolds known_oids_as_list
 * ALL THE WAY, until the oid list constants
 *
 * And so, Z3 only has to reason about the inequality of list constants,
 * which it can do efficiently without any fuel or ifuel
 *)
let lemma_oids_as_list_pairwise_ineq ()
: Lemma (BigOps.pairwise_and (fun a b -> a =!= b) (normalize_term known_oids_as_list))
= ()


(*
 * For proving the same thing about the known_oid_as_seq,
 * we have to be a little careful about normalization
 *
 * Specifically, we don't want to normalize createL or seq_of_list,
 * that's not going to lead us anywhere
 *
 * Instead the plan is to reason about them using lemma_list_seq_bij
 *)


(*
 * We write known_oids_as_seq as a List.map,
 * but postprocess it what a tactic so that its definition is expanded
 * to what is in the comments below
 *)

let norm_list_map () =
  T.norm [iota; zeta; delta_only [`%FStar.List.Tot.Base.map; `%known_oids_as_list]];
  T.trefl ()

[@ (T.postprocess_with norm_list_map)]
noextract
let known_oids_as_seq = FStar.List.Tot.Base.map Seq.createL known_oids_as_list

(*
 * known_oids_as_seq is actually:
 * [  Seq.createL oid_RIOT;
 *    Seq.createL oid_AT_CN;
 *    Seq.createL oid_AT_COUNTRY;
 *    Seq.createL oid_AT_ORGANIZATION;
 *    Seq.createL oid_CLIENT_AUTH;
 *    Seq.createL oid_AUTHORITY_KEY_IDENTIFIER;
 *    Seq.createL oid_KEY_USAGE;
 *    Seq.createL oid_EXTENDED_KEY_USAGE;
 *    Seq.createL oid_BASIC_CONSTRAINTS;
 *    Seq.createL oid_DIGEST_ALG_SHA224;
 *    Seq.createL oid_DIGEST_ALG_SHA256;
 *    Seq.createL oid_DIGEST_ALG_SHA384;
 *    Seq.createL oid_DIGEST_ALG_SHA512 ]
 *)


(*
 * Now prove the lemma
 *
 * In the arguments to the lemma, we only normalize known_oids_as_seq
 * so that pairwise_and can unfold the list into pairwise inequalities
 *
 * Anymore normalization and we will be in trouble
 *)

#push-options "--warn_error -271"
let lemma_oids_as_seq_pairwise_ineq ()
: Lemma (
  BigOps.pairwise_and (fun a b -> a =!= b)
    (Pervasives.norm [delta_only [`%known_oids_as_seq]] known_oids_as_seq)
  )

by (T.norm ([iota; zeta; delta_only [  //before sending the VC to the solver, unfold all the oids to list constants
  `%op_At;
  `%FStar.List.Tot.Base.append;
  `%oid_head_ISO_MEMBER_BODIES;
  `%oid_head_ISO_IDENTIFIED_ORG;
  `%oid_head_ISO_CCITT_DS;
  `%oid_head_ISO_ITU_COUNTRY;
  `%oid_node_COUNTRY_US;
  `%oid_node_ORGANIZATION;
  `%oid_ISO_ITU_US_ORG;
  `%oid_node_ISO_ORG_GOV;
  `%oid_GOV;
  `%oid_ID_CE;
  `%oid_NIST_ALG;
  `%oid_INTERNET;
  `%oid_PKIX;
  `%oid_AT;
  `%oid_AT_CN;
  `%oid_AT_COUNTRY;
  `%oid_AT_ORGANIZATION;
  `%oid_DOMAIN_COMPONENT;
  `%oid_AUTHORITY_KEY_IDENTIFIER;
  `%oid_KEY_USAGE;
  `%oid_EXTENDED_KEY_USAGE;
  `%oid_BASIC_CONSTRAINTS;
  `%oid_KP;
  `%oid_CLIENT_AUTH;
  `%oid_DIGEST_ALG_SHA224;
  `%oid_DIGEST_ALG_SHA256;
  `%oid_DIGEST_ALG_SHA384;
  `%oid_DIGEST_ALG_SHA512;
  `%oid_RIOT;
  `%oid_node_ORG_ANSI_X9_62;
  `%oid_ANSI_X9_62;
  `%oid_EC_ALG_UNRESTRICTED;
  `%oid_EC_GRP_SECP256R1;
  `%oid_EDWARDS_CURVE_ALGS;
  `%oid_ED25519;
  `%oid_X25519] ]))

= let aux (#a:Type) (l:list a)
    : Lemma (Seq.seq_to_list (Seq.seq_of_list l) == l)
      [SMTPat ()] = Seq.lemma_list_seq_bij l in
  ()
#pop-options

#pop-options //fuel 0 ifuel 0


(*
 * Two comments:
 *
 * We prove the FStar.List.Tot.Base.mem s known_oids_as_seq as a separate lemma below
 *
 * Why do we need this `has_type` thing, `has_type` is an internal F* thing,
 * client programs should not use it
 *)

#push-options "--fuel 0 --ifuel 1"  //need ifuel 1 to prove pattern exhaustiveness
noextract
let oid_seq_of
  (oid: oid_t)
: Tot (s: bytes { //FStar.List.Tot.Base.mem s known_oids_as_seq /\
                  Seq.length s `has_type` asn1_value_length_of_type OID })

= match oid with
  | OID_RIOT                     -> Seq.createL oid_RIOT
  | OID_AT_CN                    -> Seq.createL oid_AT_CN
  | OID_AT_COUNTRY               -> Seq.createL oid_AT_COUNTRY
  | OID_AT_ORGANIZATION          -> Seq.createL oid_AT_ORGANIZATION
  | OID_CLIENT_AUTH              -> Seq.createL oid_CLIENT_AUTH
  | OID_AUTHORITY_KEY_IDENTIFIER -> Seq.createL oid_AUTHORITY_KEY_IDENTIFIER
  | OID_KEY_USAGE                -> Seq.createL oid_KEY_USAGE
  | OID_EXTENDED_KEY_USAGE       -> Seq.createL oid_EXTENDED_KEY_USAGE
  | OID_BASIC_CONSTRAINTS        -> Seq.createL oid_BASIC_CONSTRAINTS
  // | OID_DIGEST_SHA224            -> Seq.createL oid_DIGEST_ALG_SHA224
  | OID_DIGEST_SHA256            -> Seq.createL oid_DIGEST_ALG_SHA256
  // | OID_DIGEST_SHA384            -> Seq.createL oid_DIGEST_ALG_SHA384
  // | OID_DIGEST_SHA512            -> Seq.createL oid_DIGEST_ALG_SHA512
  | OID_EC_ALG_UNRESTRICTED      -> Seq.createL oid_EC_ALG_UNRESTRICTED
  | OID_EC_GRP_SECP256R1         -> Seq.createL oid_EC_GRP_SECP256R1
  | OID_ED25519                  -> Seq.createL oid_ED25519
  | OID_X25519                   -> Seq.createL oid_X25519
#pop-options



(*
 * To prove this lemma, we just explode List.Tot.mem,
 * after that solver can do its thing
 *)
#push-options "--fuel 0 --ifuel 0"
let lemma_known_oids_as_seq_contains_oid_seq_of (oid:oid_t)
: Lemma
  (FStar.List.Tot.Base.mem (oid_seq_of oid) known_oids_as_seq)

= assert (FStar.List.Tot.Base.mem (oid_seq_of oid) known_oids_as_seq) by
    (T.norm [iota; zeta_full; delta_only [
       `%FStar.List.Tot.Base.mem;
       `%known_oids_as_seq ] ])
#pop-options

(*
 * AR: TODO: Adapt proofs below
 *)

noextract
let length_of_oid
  (oid: oid_t)
: GTot (l: asn1_value_length_of_type OID
      { l == Seq.length (oid_seq_of oid) })
= match oid with
  | OID_RIOT                     -> assert_norm (List.length oid_RIOT == 9); 9
  | OID_AT_CN                    -> assert_norm (List.length oid_AT_CN == 3); 3
  | OID_AT_COUNTRY               -> assert_norm (List.length oid_AT_COUNTRY == 3); 3
  | OID_AT_ORGANIZATION          -> assert_norm (List.length oid_AT_ORGANIZATION == 3); 3
  | OID_CLIENT_AUTH              -> assert_norm (List.length oid_CLIENT_AUTH == 7); 7
  | OID_AUTHORITY_KEY_IDENTIFIER -> assert_norm (List.length oid_AUTHORITY_KEY_IDENTIFIER == 3); 3
  | OID_KEY_USAGE                -> assert_norm (List.length oid_KEY_USAGE == 3); 3
  | OID_EXTENDED_KEY_USAGE       -> assert_norm (List.length oid_EXTENDED_KEY_USAGE == 3); 3
  | OID_BASIC_CONSTRAINTS        -> assert_norm (List.length oid_BASIC_CONSTRAINTS == 3); 3
  | OID_DIGEST_SHA256            -> assert_norm (List.length oid_DIGEST_ALG_SHA256 == 9); 9
  | OID_EC_ALG_UNRESTRICTED      -> assert_norm (List.length oid_EC_ALG_UNRESTRICTED == 5); 5
  | OID_EC_GRP_SECP256R1         -> assert_norm (List.length oid_EC_GRP_SECP256R1 == 6); 6
  | OID_ED25519                  -> assert_norm (List.length oid_ED25519 == 3); 3
  | OID_X25519                   -> assert_norm (List.length oid_X25519 == 3); 3

noextract
let filter_asn1_oid
  (l: asn1_value_length_of_type OID)
  (oid_seq: lbytes l)//{Seq.length oid_seq == l})
: GTot bool
= List.mem oid_seq known_oids_as_seq

let rec list_mem_memP (#a:eqtype) (x:a) (l:list a)
: Lemma (FStar.List.Tot.mem x l <==> FStar.List.Tot.memP x l)
= match l with
  | [] -> ()
  | hd::tl -> if hd = x then () else list_mem_memP x tl

#push-options "--fuel 0 --ifuel 0"
noextract
let synth_asn1_oid
  (l: asn1_value_length_of_type OID)
  (oid_seq: parse_filter_refine (filter_asn1_oid l))
: GTot (oid: oid_t { length_of_oid oid == l})
= lemma_oids_as_seq_pairwise_ineq ();
  let oid_seq = oid_seq <: s:bytes {List.mem s known_oids_as_seq} in

  list_mem_memP oid_seq known_oids_as_seq;
  norm_spec [iota; zeta; delta_only [`%FStar.List.Tot.memP; `%known_oids_as_seq]]
    (FStar.List.Tot.memP oid_seq known_oids_as_seq);

  if      ( oid_seq = Seq.createL oid_RIOT ) then
  ( OID_RIOT )
  else if ( oid_seq = Seq.createL oid_AT_CN ) then
  ( OID_AT_CN )
  else if ( oid_seq = Seq.createL oid_AT_COUNTRY ) then
  ( OID_AT_COUNTRY )
  else if ( oid_seq = Seq.createL oid_AT_ORGANIZATION ) then
  ( OID_AT_ORGANIZATION )
  else if ( oid_seq = Seq.createL oid_CLIENT_AUTH ) then
  ( OID_CLIENT_AUTH )
  else if ( oid_seq = Seq.createL oid_AUTHORITY_KEY_IDENTIFIER ) then
  ( OID_AUTHORITY_KEY_IDENTIFIER )
  else if ( oid_seq = Seq.createL oid_KEY_USAGE ) then
  ( OID_KEY_USAGE )
  else if ( oid_seq = Seq.createL oid_EXTENDED_KEY_USAGE ) then
  ( OID_EXTENDED_KEY_USAGE )
  else if ( oid_seq = Seq.createL oid_BASIC_CONSTRAINTS ) then
  ( OID_BASIC_CONSTRAINTS )
  // else if ( oid_seq = Seq.createL oid_DIGEST_ALG_SHA224 ) then
  // ( OID_DIGEST_SHA224 )
  else if ( oid_seq = Seq.createL oid_DIGEST_ALG_SHA256 ) then
  ( OID_DIGEST_SHA256 )
  // else if ( oid_seq = Seq.createL oid_DIGEST_ALG_SHA384 ) then
  // ( OID_DIGEST_SHA384 )
  // else if ( oid_seq = Seq.createL oid_DIGEST_ALG_SHA512 ) then
  // ( OID_DIGEST_SHA512 )
  else if ( oid_seq = Seq.createL oid_EC_ALG_UNRESTRICTED ) then
  ( OID_EC_ALG_UNRESTRICTED )
  else if ( oid_seq = Seq.createL oid_EC_GRP_SECP256R1 ) then
  ( OID_EC_GRP_SECP256R1 )
  else if ( oid_seq = Seq.createL oid_ED25519 ) then
  ( OID_ED25519 )
  else if ( oid_seq = Seq.createL oid_X25519 ) then
  ( OID_X25519 )
  else
  ( false_elim() )
#pop-options

#push-options "--warn_error -271"
let synth_asn1_oid_injective (l:asn1_value_length_of_type OID)
: Lemma (synth_injective (synth_asn1_oid l))
= let aux x x'
    : Lemma
      (requires synth_asn1_oid l x == synth_asn1_oid l x')
      (ensures x == x')
      [SMTPat ()]
    = list_mem_memP x known_oids_as_seq;
      norm_spec [iota; zeta; delta_only [`%FStar.List.Tot.memP; `%known_oids_as_seq]] (FStar.List.Tot.memP x known_oids_as_seq);
      list_mem_memP x' known_oids_as_seq;
      norm_spec [iota; zeta; delta_only [`%FStar.List.Tot.memP; `%known_oids_as_seq]] (FStar.List.Tot.memP x' known_oids_as_seq);
      lemma_oids_as_seq_pairwise_ineq () in
  ()
#pop-options

noextract
let synth_asn1_oid_inverse
  (l: asn1_value_length_of_type OID)
  (oid: oid_t { length_of_oid oid == l})
: GTot (oid_seq: parse_filter_refine (filter_asn1_oid l) { synth_asn1_oid l oid_seq == oid })
= lemma_oids_as_seq_pairwise_ineq ();
  lemma_known_oids_as_seq_contains_oid_seq_of oid;
  oid_seq_of oid

noextract
let parse_asn1_oid
  (l: asn1_value_length_of_type OID)
: parser _ (oid: oid_t { length_of_oid oid == l })
= synth_asn1_oid_injective l;
  parse_seq_flbytes l
  `parse_filter`
  filter_asn1_oid l
  `parse_synth`
  synth_asn1_oid l

noextract
let serialize_asn1_oid
  (l: asn1_value_length_of_type OID)
: serializer (parse_asn1_oid l)
= serialize_synth
  (* p1 *) (parse_seq_flbytes l
            `parse_filter`
            filter_asn1_oid l)
  (* f2 *) (synth_asn1_oid l)
  (* s1 *) (serialize_seq_flbytes l
            `serialize_filter`
            filter_asn1_oid l)
  (* g1 *) (synth_asn1_oid_inverse l)
  (* prf*) (synth_asn1_oid_injective l)

let lemma_serialize_asn1_oid_unfold
  (l: asn1_value_length_of_type OID)
  (oid: oid_t {length_of_oid oid == l})
: Lemma (
  serialize (serialize_asn1_oid l) oid ==
  serialize (serialize_seq_flbytes l) (oid_seq_of oid)
)
= serialize_synth_eq
  (* p1 *) (parse_seq_flbytes l
            `parse_filter`
            filter_asn1_oid l)
  (* f2 *) (synth_asn1_oid l)
  (* s1 *) (serialize_seq_flbytes l
            `serialize_filter`
            filter_asn1_oid l)
  (* g1 *) (synth_asn1_oid_inverse l)
  (* prf*) (synth_asn1_oid_injective l)
  (* in *) oid

let lemma_serialize_asn1_oid_size
  (l: asn1_value_length_of_type OID)
  (oid: oid_t {length_of_oid oid == l})
: Lemma (
  Seq.length (serialize (serialize_asn1_oid l) oid) == l
)
= lemma_serialize_asn1_oid_unfold l oid

(* TLV
 ======
*)
let parser_tag_of_oid
  (x: datatype_of_asn1_type OID)
: GTot (the_asn1_tag OID & asn1_value_int32_of_type OID)
= (OID, u (length_of_oid x))

noextract
let parse_asn1_oid_TLV_kind
: parser_kind
= parse_asn1_tag_kind
  `and_then_kind`
  parse_asn1_length_kind_of_type OID
  `and_then_kind`
  weak_kind_of_type OID

noextract
let synth_asn1_oid_V
  (tag: (the_asn1_tag OID & asn1_value_int32_of_type OID))
  (value: datatype_of_asn1_type OID { length_of_oid value == v (snd tag)})
: GTot (refine_with_tag parser_tag_of_oid tag)
= value

noextract
let synth_asn1_oid_V_inverse
  (tag: (the_asn1_tag OID & asn1_value_int32_of_type OID))
  (value': refine_with_tag parser_tag_of_oid tag)
: GTot (value: datatype_of_asn1_type OID
       { length_of_oid value == v (snd tag) /\
         value' == synth_asn1_oid_V tag value })
= value'

///
/// Aux parser/serialzier and lemmas
///
noextract
let parse_asn1_oid_V
  (tag: (the_asn1_tag OID & asn1_value_int32_of_type OID))
: parser (weak_kind_of_type OID) (refine_with_tag parser_tag_of_oid tag)
= weak_kind_of_type OID
  `weaken`
  parse_asn1_oid (v (snd tag))
  `parse_synth`
  synth_asn1_oid_V tag

///
/// Aux serializer
///
noextract
let serialize_asn1_oid_V
  (tag: (the_asn1_tag OID & asn1_value_int32_of_type OID))
: serializer (parse_asn1_oid_V tag)
= serialize_synth
  (* p1 *) (weak_kind_of_type OID
            `weaken`
            parse_asn1_oid (v (snd tag)))
  (* f2 *) (synth_asn1_oid_V tag)
  (* s1 *) (weak_kind_of_type OID
            `serialize_weaken`
            serialize_asn1_oid (v (snd tag)))
  (* g1 *) (synth_asn1_oid_V_inverse tag)
  (* prf*) ()

///
/// Lemmas
///

/// Reveal the computation of parse
noextract
let lemma_parse_asn1_oid_V_unfold
  (tag: (the_asn1_tag OID & asn1_value_int32_of_type OID))
  (input: bytes)
: Lemma (
  parse (parse_asn1_oid_V tag) input ==
 (match parse (parse_asn1_oid (v (snd tag))) input with
  | None -> None
  | Some (value, consumed) ->  Some (synth_asn1_oid_V tag value, consumed)))
= parse_synth_eq
  (* p1 *) (weak_kind_of_type OID
            `weaken`
            parse_asn1_oid (v (snd tag)))
  (* f2 *) (synth_asn1_oid_V tag)
  (* in *) input

/// Reveal the computation of serialzation
#push-options "--z3rlimit 16"
noextract
let lemma_serialize_asn1_oid_V_unfold
  (tag: (the_asn1_tag OID & asn1_value_int32_of_type OID))
  (value: refine_with_tag parser_tag_of_oid tag)
: Lemma (
  serialize (serialize_asn1_oid_V tag) value ==
  serialize (serialize_asn1_oid (v (snd tag))) value
)
= serialize_synth_eq
  (* p1 *) (weak_kind_of_type OID
            `weaken`
            parse_asn1_oid (v (snd tag)))
  (* f2 *) (synth_asn1_oid_V tag)
  (* s1 *) (weak_kind_of_type OID
            `serialize_weaken`
            serialize_asn1_oid (v (snd tag)))
  (* g1 *) (synth_asn1_oid_V_inverse tag)
  (* prf*) ()
  (* in *) (value)
#pop-options

///
/// TLV
///

///
/// ASN1 `OID` TLV Parser
///
noextract
let parse_asn1_oid_TLV
: parser parse_asn1_oid_TLV_kind (datatype_of_asn1_type OID)
= parse_tagged_union
  (* pt *) (parse_asn1_tag_of_type OID
            `nondep_then`
            parse_asn1_length_of_type OID)
  (* tg *) (parser_tag_of_oid)
  (* p  *) (parse_asn1_oid_V)

noextract
let filter_asn1_oid_TLV_of
  (oid: datatype_of_asn1_type OID)
  (x: datatype_of_asn1_type OID)
: GTot bool
= x = oid

noextract
let synth_asn1_oid_TLV_of
  (oid: datatype_of_asn1_type OID)
  (x: parse_filter_refine (filter_asn1_oid_TLV_of oid))
: GTot (x: datatype_of_asn1_type OID {x == oid})
= x

noextract
let parse_asn1_oid_TLV_of
  (oid: datatype_of_asn1_type OID)
: parser _ (x: datatype_of_asn1_type OID {x == oid})
= parse_asn1_oid_TLV
  `parse_filter`
  filter_asn1_oid_TLV_of oid
  `parse_synth`
  (fun x -> x <: x: datatype_of_asn1_type OID {x == oid})

///
/// Serializer
///
noextract
let serialize_asn1_oid_TLV
: serializer parse_asn1_oid_TLV
= serialize_tagged_union
  (* st *) (serialize_asn1_tag_of_type OID
            `serialize_nondep_then`
            serialize_asn1_length_of_type OID)
  (* tg *) (parser_tag_of_oid)
  (* s  *) (serialize_asn1_oid_V)

noextract
let serialize_asn1_oid_TLV_of
  (oid: datatype_of_asn1_type OID)
: serializer (parse_asn1_oid_TLV_of oid)
= serialize_synth
  (* p1 *) (parse_asn1_oid_TLV
            `parse_filter`
            filter_asn1_oid_TLV_of oid)
  (* f2 *) (fun x -> x <: x: datatype_of_asn1_type OID {x == oid})
  (* s1 *) (serialize_asn1_oid_TLV
            `serialize_filter`
            filter_asn1_oid_TLV_of oid)
  (* g1 *) (fun x -> x <: parse_filter_refine (filter_asn1_oid_TLV_of oid))
  (* prf*) ()

///
/// Lemmas
///

(* FIXME: Sometimes will fail *)
// /// Reveal the computation of parse
// #restart-solver
// #push-options "--z3rlimit 64 --initial_ifuel 8"
// noextract
// let lemma_parse_asn1_oid_TLV_unfold
//   (input: bytes)
// : Lemma (
//   parse parse_asn1_oid_TLV input ==
//  (match parse (parse_asn1_tag_of_type OID) input with
//   | None -> None
//   | Some (tag, consumed_tag) ->
//     (let input_LV = Seq.slice input consumed_tag (Seq.length input) in
//      match parse (parse_asn1_length_of_type OID) input_LV with
//      | None -> None
//      | Some (len, consumed_len) ->
//        (let input_V = Seq.slice input_LV consumed_len (Seq.length input_LV) in
//         match parse (parse_asn1_oid_V (tag, len)) input_V with
//         | None -> None
//         | Some (value, consumed_value) ->
//                Some ((synth_asn1_oid_V (tag,len) value),
//                      (consumed_tag + consumed_len + consumed_value <: consumed_length input)))
//      ))
// )
// = nondep_then_eq
//   (* p1 *) (parse_asn1_tag_of_type OID)
//   (* p2 *) (parse_asn1_length_of_type OID)
//   (* in *) (input)

//   let parsed_tag
//   = parse (parse_asn1_tag_of_type OID
//            `nondep_then`
//            parse_asn1_length_of_type OID) input in
//   if (Some? parsed_tag) then
//   ( let Some (tag, consumed) = parsed_tag in
//     lemma_parse_asn1_oid_V_unfold tag (Seq.slice input consumed (Seq.length input)) )

//   parse_tagged_union_eq
//   (* pt *) (parse_asn1_tag_of_type OID
//             `nondep_then`
//             parse_asn1_length_of_type OID)
//   (* tg *) (parser_tag_of_oid)
//   (* p  *) (parse_asn1_oid_V)
//   (* in *) (input)
// #pop-options

/// Reveal the computation of serialize
#push-options "--z3rlimit 32"
noextract
let lemma_serialize_asn1_oid_TLV_unfold
  (value: datatype_of_asn1_type OID)
: Lemma (
  serialize serialize_asn1_oid_TLV value ==
  serialize (serialize_asn1_tag_of_type OID) OID
  `Seq.append`
  serialize (serialize_asn1_length_of_type OID) (u (length_of_oid value))
  `Seq.append`
  serialize (serialize_asn1_oid (length_of_oid value)) value
)
= serialize_nondep_then_eq
  (* s1 *) (serialize_asn1_tag_of_type OID)
  (* s2 *) (serialize_asn1_length_of_type OID)
  (* in *) (parser_tag_of_oid value);
  lemma_serialize_asn1_oid_V_unfold (parser_tag_of_oid value) value;
  serialize_tagged_union_eq
  (* st *) (serialize_asn1_tag_of_type OID
            `serialize_nondep_then`
            serialize_asn1_length_of_type OID)
  (* tg *) (parser_tag_of_oid)
  (* s  *) (serialize_asn1_oid_V)
  (* in *) (value)

noextract
let lemma_serialize_asn1_oid_TLV_of_unfold
  (oid: datatype_of_asn1_type OID)
  (value: datatype_of_asn1_type OID{value == oid})
: Lemma (
  serialize (serialize_asn1_oid_TLV_of oid) value ==
  serialize (serialize_asn1_tag_of_type OID) OID
  `Seq.append`
  serialize (serialize_asn1_length_of_type OID) (u (length_of_oid value))
  `Seq.append`
  serialize (serialize_asn1_oid (length_of_oid value)) value
)
= lemma_serialize_asn1_oid_TLV_unfold oid;
  serialize_synth_eq
  (* p1 *) (parse_asn1_oid_TLV
            `parse_filter`
            filter_asn1_oid_TLV_of oid)
  (* f2 *) (fun x -> x <: x: datatype_of_asn1_type OID {x == oid})
  (* s1 *) (serialize_asn1_oid_TLV
            `serialize_filter`
            filter_asn1_oid_TLV_of oid)
  (* g1 *) (fun x -> x <: parse_filter_refine (filter_asn1_oid_TLV_of oid))
  (* prf*) ()
  (* in *) value
#pop-options

/// Reveal the size of a serialzation
#push-options "--z3rlimit 16"
noextract
let lemma_serialize_asn1_oid_TLV_size
  (value: datatype_of_asn1_type OID)
: Lemma (
  Seq.length (serialize serialize_asn1_oid_TLV value) ==
  1 + length_of_asn1_length (u (length_of_oid value)) + length_of_oid value
)
= lemma_serialize_asn1_oid_TLV_unfold value;
  lemma_serialize_asn1_tag_of_type_size OID OID;
  lemma_serialize_asn1_length_size (u (length_of_oid value));
  serialize_asn1_length_of_type_eq OID (u (length_of_oid value));
  lemma_serialize_asn1_oid_size (length_of_oid value) value

noextract
let lemma_serialize_asn1_oid_TLV_of_size
  (oid: datatype_of_asn1_type OID)
  (value: datatype_of_asn1_type OID{value == oid})
: Lemma (
  Seq.length (serialize (serialize_asn1_oid_TLV_of oid) value) ==
  1 + length_of_asn1_length (u (length_of_oid value)) + length_of_oid value
)
= lemma_serialize_asn1_oid_TLV_of_unfold oid value;
  lemma_serialize_asn1_tag_of_type_size OID OID;
  lemma_serialize_asn1_length_size (u (length_of_oid value));
  serialize_asn1_length_of_type_eq OID (u (length_of_oid value));
  lemma_serialize_asn1_oid_size (length_of_oid value) value
#pop-options

(* Useful combinators to construct simple OID-enveloped sequence *)
let parse_envelop_OID_with
  (oid: datatype_of_asn1_type OID)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
: parser _ (x: datatype_of_asn1_type OID {x == oid} `tuple2` t)
= parse_asn1_oid_TLV_of oid
  `nondep_then`
  p

let serialize_envelop_OID_with
  (oid: datatype_of_asn1_type OID)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
: serializer (parse_envelop_OID_with oid s)
= serialize_asn1_oid_TLV_of oid
  `serialize_nondep_then`
  s

let lemma_serialize_envelop_OID_with_unfold
  (oid: datatype_of_asn1_type OID)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (x: (x: datatype_of_asn1_type OID {x == oid} `tuple2` t))
: Lemma (
  serialize (serialize_envelop_OID_with oid s) x ==
  serialize (serialize_asn1_oid_TLV_of oid) (fst x)
  `Seq.append`
  serialize s (snd x)
)
= serialize_nondep_then_eq
  (* s1 *) (serialize_asn1_oid_TLV_of oid)
  (* s2 *) s
  (* in *) x

let lemma_serialize_envelop_OID_with_size
  (oid: datatype_of_asn1_type OID)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (x: (x: datatype_of_asn1_type OID {x == oid} `tuple2` t))
: Lemma (
  length_of_opaque_serialization (serialize_envelop_OID_with oid s) x ==
  length_of_opaque_serialization (serialize_asn1_oid_TLV_of oid) (fst x) +
  length_of_opaque_serialization s (snd x)
)
= lemma_serialize_envelop_OID_with_unfold oid s x
