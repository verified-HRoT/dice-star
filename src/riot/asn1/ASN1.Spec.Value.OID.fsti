module ASN1.Spec.Value.OID

open ASN1.Spec.Base

open ASN1.Base
open ASN1.Spec.Tag
open ASN1.Spec.Length
open LowParse.Spec.SeqBytes.Base

open FStar.Integers

unfold noextract
let ( @ ) = List.Tot.Base.append

unfold let lu8
= l: list UInt8.t
  { asn1_length_inbound
      (List.length l)
      (asn1_value_length_min_of_type OID)
      (asn1_value_length_max_of_type OID) }

unfold let llu8
  (l: asn1_value_length_of_type OID )
= List.llist UInt8.t l

(* Actually we need to expose all if we want to prove the actual content of serialization. *)

(* Top level OID tuples
  =====================
#define MBEDTLS_OID_ISO_MEMBER_BODIES           "\x2a"          /* {iso(1) member-body(2)} */
#define MBEDTLS_OID_ISO_IDENTIFIED_ORG          "\x2b"          /* {iso(1) identified-organization(3)} */
#define MBEDTLS_OID_ISO_CCITT_DS                "\x55"          /* {joint-iso-ccitt(2) ds(5)} */
#define MBEDTLS_OID_ISO_ITU_COUNTRY             "\x60"          /* {joint-iso-itu-t(2) country(16)} */
*)
// noextract inline_for_extraction val oid_head_ISO_MEMBER_BODIES : lu8
// noextract inline_for_extraction val oid_head_ISO_IDENTIFIED_ORG : lu8
// noextract inline_for_extraction val oid_head_ISO_CCITT_DS : lu8
// noextract inline_for_extraction val oid_head_ISO_ITU_COUNTRY : lu8

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
// noextract inline_for_extraction val oid_node_COUNTRY_US : lu8
// noextract inline_for_extraction val oid_node_ORG_RSA_DATA_SECURITY : lu8
// noextract inline_for_extraction val oid_RSA_COMPANY : lu8
// noextract inline_for_extraction val oid_node_ORG_ANSI_X9_62 : lu8
// noextract inline_for_extraction val oid_ANSI_X9_62 : lu8

(* ISO ITU OID parts
  ==================
#define MBEDTLS_OID_ORGANIZATION                "\x01"          /* {organization(1)} */
#define MBEDTLS_OID_ISO_ITU_US_ORG              MBEDTLS_OID_ISO_ITU_COUNTRY MBEDTLS_OID_COUNTRY_US MBEDTLS_OID_ORGANIZATION /* {joint-iso-itu-t(2) country(16) us(840) organization(1)} */

#define MBEDTLS_OID_ORG_GOV                     "\x65"          /* {gov(101)} */
#define MBEDTLS_OID_GOV                         MBEDTLS_OID_ISO_ITU_US_ORG MBEDTLS_OID_ORG_GOV /* {joint-iso-itu-t(2) country(16) us(840) organization(1) gov(101)} */

#define MBEDTLS_OID_ORG_NETSCAPE                "\x86\xF8\x42"  /* {netscape(113730)} */
#define MBEDTLS_OID_NETSCAPE                    MBEDTLS_OID_ISO_ITU_US_ORG MBEDTLS_OID_ORG_NETSCAPE /* Netscape OID {joint-iso-itu-t(2) country(16) us(840) organization(1) netscape(113730)} */
*)
// noextract inline_for_extraction val oid_node_ORGANIZATION : lu8
// noextract inline_for_extraction val oid_ISO_ITU_US_ORG : lu8
// noextract inline_for_extraction val oid_node_ISO_ORG_GOV : lu8
// noextract inline_for_extraction val oid_GOV : lu8

(* ISO arc for standard certificate and CRL extensions
  =====================================================
#define MBEDTLS_OID_ID_CE                       MBEDTLS_OID_ISO_CCITT_DS "\x1D" /**< id-ce OBJECT IDENTIFIER  ::=  {joint-iso-ccitt(2) ds(5) 29} */

#define MBEDTLS_OID_NIST_ALG                    MBEDTLS_OID_GOV "\x03\x04" /** { joint-iso-itu-t(2) country(16) us(840) organization(1) gov(101) csor(3) nistAlgorithm(4) */
*)
// noextract inline_for_extraction val oid_ID_CE : lu8

// noextract inline_for_extraction val oid_NIST_ALG : lu8

(* Private Internet Extensions
   { iso(1) identified-organization(3) dod(6) internet(1)
                        security(5) mechanisms(5) pkix(7) }
  =========================================================
#define MBEDTLS_OID_INTERNET                    MBEDTLS_OID_ISO_IDENTIFIED_ORG MBEDTLS_OID_ORG_DOD "\x01"
#define MBEDTLS_OID_PKIX                        MBEDTLS_OID_INTERNET "\x05\x05\x07"
*)
// noextract inline_for_extraction val oid_INTERNET : lu8
// noextract inline_for_extraction val oid_PKIX : lu8

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
// noextract inline_for_extraction val oid_AT : lu8 (* id-at OBJECT IDENTIFIER ::= {joint-iso-ccitt(2) ds(5) 4} *)
noextract inline_for_extraction val oid_AT_CN : llu8 3           (* id-at-commonName AttributeType:= {id-at 3} *)
// noextract let oid_AT_SUR_NAME             = normalize_term(oid_AT @ [0x04uy]           (* id-at-surName AttributeType:= {id-at 4} *))
// noextract let oid_AT_SERIAL_NUMBER        = normalize_term(oid_AT @ [0x05uy]           (* id-at-serialNumber AttributeType:= {id-at 5} *))
noextract inline_for_extraction val oid_AT_COUNTRY : llu8 3           (* id-at-countryName AttributeType:= {id-at 6} *)
// noextract let oid_AT_LOCALITY             = normalize_term(oid_AT @ [0x07uy]           (* id-at-locality AttributeType:= {id-at 7} *))
// noextract let oid_AT_STATE                = normalize_term(oid_AT @ [0x08uy]           (* id-at-state AttributeType:= {id-at 8} *))
noextract inline_for_extraction val oid_AT_ORGANIZATION : llu8 3          (* id-at-organizationName AttributeType:= {id-at 10} *)
// noextract let oid_AT_ORG_UNIT             = normalize_term(oid_AT @ [0x0Buy]           (* id-at-organizationalUnitName AttributeType:= {id-at 11} *))
// noextract let oid_AT_TITLE                = normalize_term(oid_AT @ [0x0Cuy]           (* id-at-title AttributeType:= {id-at 12} *))
// noextract let oid_AT_POSTAL_ADDRESS       = normalize_term(oid_AT @ [0x10uy]           (* id-at-postalAddress AttributeType:= {id-at 16} *))
// noextract let oid_AT_POSTAL_CODE          = normalize_term(oid_AT @ [0x11uy]           (* id-at-postalCode AttributeType:= {id-at 17} *))
// noextract let oid_AT_GIVEN_NAME           = normalize_term(oid_AT @ [0x2Auy]           (* id-at-givenName AttributeType:= {id-at 42} *))
// noextract let oid_AT_INITIALS             = normalize_term(oid_AT @ [0x2Buy]           (* id-at-initials AttributeType:= {id-at 43} *))
// noextract let oid_AT_GENERATION_QUALIFIER = normalize_term(oid_AT @ [0x2Cuy]           (* id-at-generationQualifier AttributeType:= {id-at 44} *))
// noextract let oid_AT_UNIQUE_IDENTIFIER    = normalize_term(oid_AT @ [0x2Duy]           (* id-at-uniqueIdentifier AttributType:= {id-at 45} *))
// noextract let oid_AT_DN_QUALIFIER         = normalize_term(oid_AT @ [0x2Euy]           (* id-at-dnQualifier AttributeType:= {id-at 46} *))
// noextract let oid_AT_PSEUDONYM            = normalize_term(oid_AT @ [0x41uy]           (* id-at-pseudonym AttributeType:= {id-at 65} *))

// noextract inline_for_extraction val oid_DOMAIN_COMPONENT : lu8 (* id-domainComponent AttributeType:= {itu-t(0) data(9) pss(2342) ucl(19200300) pilot(100) pilotAttributeType(1) domainComponent(25)} *)


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
noextract inline_for_extraction val oid_AUTHORITY_KEY_IDENTIFIER : llu8 3
noextract inline_for_extraction val oid_KEY_USAGE : llu8 3
noextract inline_for_extraction val oid_EXTENDED_KEY_USAGE : llu8 3
noextract inline_for_extraction val oid_BASIC_CONSTRAINTS : llu8 3

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
// noextract inline_for_extraction val oid_KP : lu8
noextract inline_for_extraction val oid_CLIENT_AUTH : llu8 7

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
// noextract inline_for_extraction val oid_DIGEST_ALG_SHA224 : lu8
noextract inline_for_extraction val oid_DIGEST_ALG_SHA256 : llu8 9
// noextract inline_for_extraction val oid_DIGEST_ALG_SHA384 : lu8
// noextract inline_for_extraction val oid_DIGEST_ALG_SHA512 : lu8

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

noextract inline_for_extraction val oid_EC_ALG_UNRESTRICTED : llu8 5

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

noextract inline_for_extraction val oid_EC_GRP_SECP256R1 : llu8 6

// noextract inline_for_extraction val oid_EDWARDS_CURVE_ALGS : lu8

noextract inline_for_extraction val oid_ED25519 : llu8 3

noextract inline_for_extraction val oid_X25519 : llu8 3

(*
/*
 * PKCS definition OIDs
 */

#define MBEDTLS_OID_PKCS                MBEDTLS_OID_RSA_COMPANY "\x01" /**< pkcs OBJECT IDENTIFIER ::= { iso(1) member-body(2) us(840) rsadsi(113549) 1 } */
#define MBEDTLS_OID_PKCS1               MBEDTLS_OID_PKCS "\x01" /**< pkcs-1 OBJECT IDENTIFIER ::= { iso(1) member-body(2) us(840) rsadsi(113549) pkcs(1) 1 } */
#define MBEDTLS_OID_PKCS5               MBEDTLS_OID_PKCS "\x05" /**< pkcs-5 OBJECT IDENTIFIER ::= { iso(1) member-body(2) us(840) rsadsi(113549) pkcs(1) 5 } */
#define MBEDTLS_OID_PKCS9               MBEDTLS_OID_PKCS "\x09" /**< pkcs-9 OBJECT IDENTIFIER ::= { iso(1) member-body(2) us(840) rsadsi(113549) pkcs(1) 9 } */
#define MBEDTLS_OID_PKCS12              MBEDTLS_OID_PKCS "\x0c" /**< pkcs-12 OBJECT IDENTIFIER ::= { iso(1) member-body(2) us(840) rsadsi(113549) pkcs(1) 12 } */
*)

// noextract inline_for_extraction val oid_PKCS : lu8
// noextract inline_for_extraction val oid_PKCS9 : lu8

(*
/*
 * PKCS#8 OIDs
 */
#define MBEDTLS_OID_PKCS9_CSR_EXT_REQ           MBEDTLS_OID_PKCS9 "\x0e" /**< extensionRequest OBJECT IDENTIFIER ::= {pkcs-9 14} */
*)

noextract inline_for_extraction val oid_PKCS9_CSR_EXT_REQ : llu8 9

(* RIoT OID
  =========
1.3.6.1.4.1.311.89.3.1
*)
(* FIXME: Check RIoT's OID *)
noextract inline_for_extraction val oid_RIOT : llu8 9

noextract
let oid_seq_of
  (oid: oid_t)
: Tot (s: bytes { asn1_length_inbound (Seq.length s) (asn1_value_length_min_of_type OID) (asn1_value_length_max_of_type OID) })
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
  | OID_PKCS9_CSR_EXT_REQ        -> Seq.createL oid_PKCS9_CSR_EXT_REQ

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
  | OID_PKCS9_CSR_EXT_REQ        -> assert_norm (List.length oid_PKCS9_CSR_EXT_REQ == 9); 9

// noextract
// let length_of_oid
//   (oid: oid_t)
// : GTot (l: asn1_value_length_of_type OID)
// = match oid with
//   | OID_RIOT                     -> 9
//   | OID_AT_CN                    -> 3
//   | OID_AT_COUNTRY               -> 3
//   | OID_AT_ORGANIZATION          -> 3
//   | OID_CLIENT_AUTH              -> 7
//   | OID_AUTHORITY_KEY_IDENTIFIER -> 3
//   | OID_KEY_USAGE                -> 3
//   | OID_EXTENDED_KEY_USAGE       -> 3
//   | OID_BASIC_CONSTRAINTS        -> 3
//   | OID_DIGEST_SHA256            -> 9
//   | OID_EC_ALG_UNRESTRICTED      -> 5
//   | OID_EC_GRP_SECP256R1         -> 6
//   | OID_ED25519                  -> 3
//   | OID_X25519                   -> 3
//   | OID_PKCS9_CSR_EXT_REQ        -> 9

// noextract
// val filter_asn1_oid
//   (l: asn1_value_length_of_type OID)
//   (oid_seq: lbytes l)//{Seq.length oid_seq == l})
// : GTot bool

// noextract
// val synth_asn1_oid
//   (l: asn1_value_length_of_type OID)
//   (oid_seq: parse_filter_refine (filter_asn1_oid l))
// : GTot (oid: oid_t { length_of_oid oid == l})

// val synth_asn1_oid_injective (l:asn1_value_length_of_type OID)
// : Lemma (synth_injective (synth_asn1_oid l))

// noextract
// val synth_asn1_oid_inverse
//   (l: asn1_value_length_of_type OID)
//   (oid: oid_t { length_of_oid oid == l})
// : GTot (oid_seq: parse_filter_refine (filter_asn1_oid l) { synth_asn1_oid l oid_seq == oid })

noextract
val parse_asn1_oid
  (l: asn1_value_length_of_type OID)
: parser (parse_filter_kind (total_constant_size_parser_kind l)) (oid: oid_t { length_of_oid oid == l })

noextract
val serialize_asn1_oid
  (l: asn1_value_length_of_type OID)
: serializer (parse_asn1_oid l)

val lemma_serialize_asn1_oid_unfold
  (l: asn1_value_length_of_type OID)
  (oid: oid_t {length_of_oid oid == l})
: Lemma (
  serialize (serialize_asn1_oid l) oid ==
  serialize (serialize_seq_flbytes l) (oid_seq_of oid)
)

val lemma_serialize_asn1_oid_size
  (l: asn1_value_length_of_type OID)
  (oid: oid_t {length_of_oid oid == l})
: Lemma (
  Seq.length (serialize (serialize_asn1_oid l) oid) == l
)

(* TLV
 ======
*)

inline_for_extraction noextract
let parse_asn1_oid_TLV_kind
: parser_kind
= parse_asn1_tag_kind
  `and_then_kind`
  parse_asn1_length_kind_of_type OID
  `and_then_kind`
  weak_kind_of_type OID

///
/// ASN1 `OID` TLV Parser
///
noextract
val parse_asn1_oid_TLV
: parser parse_asn1_oid_TLV_kind (datatype_of_asn1_type OID)

noextract
let filter_asn1_oid_TLV_of
  (oid: datatype_of_asn1_type OID)
  (x: datatype_of_asn1_type OID)
: Tot bool
= x = oid

let the_asn1_oid
  (oid: datatype_of_asn1_type OID)
= parse_filter_refine (filter_asn1_oid_TLV_of oid)

noextract
let parse_asn1_oid_TLV_of
  (oid: datatype_of_asn1_type OID)
: parser (parse_filter_kind parse_asn1_oid_TLV_kind) (the_asn1_oid oid)
= parse_asn1_oid_TLV
  `parse_filter`
  filter_asn1_oid_TLV_of oid

///
/// Serializer
///
noextract
val serialize_asn1_oid_TLV
: serializer parse_asn1_oid_TLV

noextract
let serialize_asn1_oid_TLV_of
  (oid: datatype_of_asn1_type OID)
: serializer (parse_asn1_oid_TLV_of oid)
= serialize_asn1_oid_TLV
  `serialize_filter`
  filter_asn1_oid_TLV_of oid

val lemma_serialize_asn1_oid_TLV_unfold
  (value: datatype_of_asn1_type OID)
: Lemma (
  serialize serialize_asn1_oid_TLV value ==
  serialize (serialize_asn1_tag_of_type OID) OID
  `Seq.append`
  serialize (serialize_asn1_length_of_type OID) (u (length_of_oid value))
  `Seq.append`
  serialize (serialize_asn1_oid (length_of_oid value)) value
)

val lemma_serialize_asn1_oid_TLV_of_unfold
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

/// Reveal the size of a serialzation

val lemma_serialize_asn1_oid_TLV_size
  (value: datatype_of_asn1_type OID)
: Lemma (
  Seq.length (serialize serialize_asn1_oid_TLV value) ==
  1 + length_of_asn1_length (u (length_of_oid value)) + length_of_oid value
)

val lemma_serialize_asn1_oid_TLV_of_size
  (oid: datatype_of_asn1_type OID)
  (value: datatype_of_asn1_type OID{value == oid})
: Lemma (
  Seq.length (serialize (serialize_asn1_oid_TLV_of oid) value) ==
  1 + length_of_asn1_length (u (length_of_oid value)) + length_of_oid value /\
  Seq.length (serialize (serialize_asn1_oid_TLV_of oid) value) ==
  Seq.length (serialize (serialize_asn1_oid_TLV) value)
)

(* Useful combinators to construct simple OID-enveloped sequence *)
let envelop_OID_with_t
  (oid: datatype_of_asn1_type OID)
  (t: Type0)
= parse_filter_refine (filter_asn1_oid_TLV_of oid) `tuple2` t

val parse_envelop_OID_with
  (oid: datatype_of_asn1_type OID)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
: parser (and_then_kind (parse_filter_kind parse_asn1_oid_TLV_kind) k) (oid `envelop_OID_with_t` t)

val serialize_envelop_OID_with
  (oid: datatype_of_asn1_type OID)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
: serializer (parse_envelop_OID_with oid s)

unfold
let predicate_serialize_envelop_OID_with_unfold
  (oid: datatype_of_asn1_type OID)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (x: oid `envelop_OID_with_t` t)
: Type0
= serialize (serialize_envelop_OID_with oid s) x ==
  serialize (serialize_asn1_oid_TLV_of oid) (fst x)
  `Seq.append`
  serialize s (snd x)

val lemma_serialize_envelop_OID_with_unfold
  (oid: datatype_of_asn1_type OID)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (x: oid `envelop_OID_with_t` t)
: Lemma (
  predicate_serialize_envelop_OID_with_unfold oid s x
)

let length_of_envelop_OID_with
  (oid: datatype_of_asn1_type OID)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (x: t)
= length_of_opaque_serialization (serialize_asn1_oid_TLV_of oid) oid +
  length_of_opaque_serialization s x

unfold
let predicate_serialize_envelop_OID_with_size
  (oid: datatype_of_asn1_type OID)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (x: oid `envelop_OID_with_t` t)
: Type0
= length_of_opaque_serialization (serialize_envelop_OID_with oid s) x
  == length_of_envelop_OID_with oid s (snd x)

val lemma_serialize_envelop_OID_with_size
  (oid: datatype_of_asn1_type OID)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (x: oid `envelop_OID_with_t` t)
: Lemma (
  predicate_serialize_envelop_OID_with_size oid s x
)
