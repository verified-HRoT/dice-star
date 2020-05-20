module ASN1.Spec.Value.OID

open LowParse.Spec.Base
open LowParse.Spec.Combinators

open ASN1.Base
open ASN1.Spec.Tag
open ASN1.Spec.Length
open LowParse.Spec.SeqBytes.Base

open FStar.Integers

let ( @ ) = List.append

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
noextract let oid_node_COUNTRY_US = [0x86uy; 0x48uy]

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

(* RIoT OID
  =========
1.3.6.1.4.1.311.89.3.1
*)
(* FIXME: Check RIoT's OID *)
noextract let oid_RIOT = oid_INTERNET @ [0x04uy; 0x01uy; 0x82uy; 0x37uy; 0x59uy; 0x03uy; 0x01uy]

(* Known OIDs *)
#push-options "--z3rlimit 64 --fuel 32 --ifuel 1"
noextract
let known_oids_as_list: l: list _ {List.Tot.Base.no_repeats_p (normalize_term l)}
= [ oid_RIOT;
    oid_AT_CN;
    oid_AT_COUNTRY;
    oid_AT_ORGANIZATION;
    oid_CLIENT_AUTH;
    oid_AUTHORITY_KEY_IDENTIFIER;
    oid_KEY_USAGE;
    oid_EXTENDED_KEY_USAGE;
    oid_BASIC_CONSTRAINTS;
    oid_DIGEST_ALG_SHA224;
    oid_DIGEST_ALG_SHA256;
    oid_DIGEST_ALG_SHA384;
    oid_DIGEST_ALG_SHA512 ]
#pop-options

let lemma_oids_as_list_pairwise_ineq ()
: Lemma (
  BigOps.pairwise_and (fun a b -> a =!= b) (normalize_term known_oids_as_list))
= ()

#push-options "--z3rlimit 64 --fuel 32 --ifuel 1"
noextract
let known_oids_as_seq: l: list _ {List.Tot.Base.no_repeats_p (normalize_term l)}
= (List.Tot.map Seq.createL known_oids_as_list)

// let lemma_oids_as_seq_pairwise_ineq ()
// : Lemma (
//   BigOps.pairwise_and (fun a b -> a =!= b) (normalize_term known_oids_as_seq))
// = assert (List.Tot.Base.no_repeats_p (known_oids_as_seq))
#pop-options

#push-options "--query_stats --z3rlimit 128 --fuel 16"
noextract
let oid_seq_of
  (oid: oid_t)
: Tot (s: bytes { List.mem s known_oids_as_seq /\
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
  | OID_DIGEST_SHA224            -> Seq.createL oid_DIGEST_ALG_SHA224
  | OID_DIGEST_SHA256            -> Seq.createL oid_DIGEST_ALG_SHA256
  | OID_DIGEST_SHA384            -> Seq.createL oid_DIGEST_ALG_SHA384
  | OID_DIGEST_SHA512            -> Seq.createL oid_DIGEST_ALG_SHA512
#pop-options

noextract
let length_of_oid
  (oid: oid_t)
: GTot (l: asn1_value_length_of_type OID
      { l == Seq.length (oid_seq_of oid) })
= match oid with
  | OID_RIOT                     -> normalize_term (List.length oid_RIOT)
  | OID_AT_CN                    -> normalize_term (List.length oid_AT_CN)
  | OID_AT_COUNTRY               -> normalize_term (List.length oid_AT_COUNTRY)
  | OID_AT_ORGANIZATION          -> normalize_term (List.length oid_AT_ORGANIZATION)
  | OID_CLIENT_AUTH              -> normalize_term (List.length oid_CLIENT_AUTH)
  | OID_AUTHORITY_KEY_IDENTIFIER -> normalize_term (List.length oid_AUTHORITY_KEY_IDENTIFIER)
  | OID_KEY_USAGE                -> normalize_term (List.length oid_KEY_USAGE)
  | OID_EXTENDED_KEY_USAGE       -> normalize_term (List.length oid_EXTENDED_KEY_USAGE)
  | OID_BASIC_CONSTRAINTS        -> normalize_term (List.length oid_BASIC_CONSTRAINTS)
  | OID_DIGEST_SHA224            -> assert_norm (List.length (oid_DIGEST_ALG_SHA224) == 9); 9
  | OID_DIGEST_SHA256            -> assert_norm (List.length (oid_DIGEST_ALG_SHA256) == 9); 9
  | OID_DIGEST_SHA384            -> assert_norm (List.length (oid_DIGEST_ALG_SHA384) == 9); 9
  | OID_DIGEST_SHA512            -> assert_norm (List.length (oid_DIGEST_ALG_SHA512) == 9); 9

noextract
let filter_asn1_oid
  (l: asn1_value_length_of_type OID)
  (oid_seq: lbytes l)//{Seq.length oid_seq == l})
: GTot bool
= List.mem oid_seq known_oids_as_seq

#push-options "--query_stats --z3rlimit 64 --fuel 16"
noextract
let synth_asn1_oid
  (l: asn1_value_length_of_type OID)
  (oid_seq: parse_filter_refine (filter_asn1_oid l))
: GTot (oid: oid_t { length_of_oid oid == l})
= let oid_seq = oid_seq <: bytes in
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
  else if ( oid_seq = Seq.createL oid_DIGEST_ALG_SHA224 ) then
  ( OID_DIGEST_SHA224 )
  else if ( oid_seq = Seq.createL oid_DIGEST_ALG_SHA256 ) then
  ( OID_DIGEST_SHA256 )
  else if ( oid_seq = Seq.createL oid_DIGEST_ALG_SHA384 ) then
  ( OID_DIGEST_SHA384 )
  else if ( oid_seq = Seq.createL oid_DIGEST_ALG_SHA512 ) then
  ( OID_DIGEST_SHA512 )
  else
  ( false_elim () )

noextract
let synth_asn1_oid_inverse
  (l: asn1_value_length_of_type OID)
  (oid: oid_t { length_of_oid oid == l})
: GTot (oid_seq: parse_filter_refine (filter_asn1_oid l) { synth_asn1_oid l oid_seq == oid })
= oid_seq_of oid

noextract
let parse_asn1_oid
  (l: asn1_value_length_of_type OID)
: parser _ (oid: oid_t { length_of_oid oid == l })
= parse_seq_flbytes l
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
  (* prf*) ()

let serialize_asn1_oid_unfold
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
  (* prf*) ()
  (* in *) oid

let serialize_asn1_oid_size
  (l: asn1_value_length_of_type OID)
  (oid: oid_t {length_of_oid oid == l})
: Lemma (
  Seq.length (serialize (serialize_asn1_oid l) oid) == l
)
= serialize_asn1_oid_unfold l oid


(* TLV
 ======
*)
let parser_tag_of_oid
  (x: datatype_of_asn1_type OID)
: GTot (the_asn1_type OID & asn1_value_int32_of_type OID)
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
  (tag: (the_asn1_type OID & asn1_value_int32_of_type OID))
  (value: datatype_of_asn1_type OID { length_of_oid value == v (snd tag)})
: GTot (refine_with_tag parser_tag_of_oid tag)
= value

(* FIXME: Broke after adding more OIDs. *)
noextract
let synth_asn1_oid_V_inverse
  (tag: (the_asn1_type OID & asn1_value_int32_of_type OID))
  (value': refine_with_tag parser_tag_of_oid tag)
: GTot (value: datatype_of_asn1_type OID
       { length_of_oid value == v (snd tag) /\
         value' == synth_asn1_oid_V tag value })
= admit();
  value'

///
/// Aux parser/serialzier and lemmas
///
noextract
let parse_asn1_oid_V
  (tag: (the_asn1_type OID & asn1_value_int32_of_type OID))
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
  (tag: (the_asn1_type OID & asn1_value_int32_of_type OID))
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
let parse_asn1_oid_V_unfold
  (tag: (the_asn1_type OID & asn1_value_int32_of_type OID))
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
noextract
let serialize_asn1_oid_V_unfold
  (tag: (the_asn1_type OID & asn1_value_int32_of_type OID))
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

///
/// Lemmas
///

(* FIXME: Sometimes will fail *)
// /// Reveal the computation of parse
// #restart-solver
// #push-options "--query_stats --z3rlimit 64 --initial_ifuel 8"
// noextract
// let parse_asn1_oid_TLV_unfold
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
//     parse_asn1_oid_V_unfold tag (Seq.slice input consumed (Seq.length input)) )

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
let serialize_asn1_oid_TLV_unfold
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
  serialize_asn1_oid_V_unfold (parser_tag_of_oid value) value;
  serialize_tagged_union_eq
  (* st *) (serialize_asn1_tag_of_type OID
            `serialize_nondep_then`
            serialize_asn1_length_of_type OID)
  (* tg *) (parser_tag_of_oid)
  (* s  *) (serialize_asn1_oid_V)
  (* in *) (value)
#pop-options

/// Reveal the size of a serialzation
#push-options "--z3rlimit 16"
noextract
let serialize_asn1_oid_TLV_size
  (value: datatype_of_asn1_type OID)
: Lemma (
  Seq.length (serialize serialize_asn1_oid_TLV value) ==
  1 + length_of_asn1_length (u (length_of_oid value)) + length_of_oid value
)
= serialize_asn1_oid_TLV_unfold value;
  serialize_asn1_tag_of_type_size OID OID;
  serialize_asn1_length_size (u (length_of_oid value));
  serialize_asn1_length_of_type_eq OID (u (length_of_oid value));
  serialize_asn1_oid_size (length_of_oid value) value
#pop-options

