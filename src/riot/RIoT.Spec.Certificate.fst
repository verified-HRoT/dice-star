module RIoT.Spec.Certificate

open ASN1.Spec
open X509

open RIoT.Base
open RIoT.Declassify
open RIoT.X509

open Lib.IntTypes

module B32 = FStar.Bytes
module B = LowStar.Buffer
module IB = LowStar.ImmutableBuffer
module HS  = FStar.HyperStack
module HST = FStar.HyperStack.ST

#set-options "--z3rlimit 512 --fuel 0 --ifuel 0 --admit_smt_queries true"

(* Create AliasKey To-Be-Signed Certificate
  =======================================
  RFC 5280:
     TBSCertificate  ::=  SEQUENCE  {
        version         [0]  EXPLICIT Version DEFAULT v1,
        serialNumber         CertificateSerialNumber,
        signature            AlgorithmIdentifier,
        issuer               Name,
        validity             Validity,
        subject              Name,
        subjectPublicKeyInfo SubjectPublicKeyInfo,
        issuerUniqueID  [1]  IMPLICIT UniqueIdentifier OPTIONAL,
                             -- If present, version MUST be v2 or v3
        subjectUniqueID [2]  IMPLICIT UniqueIdentifier OPTIONAL,
                             -- If present, version MUST be v2 or v3
        extensions      [3]  EXPLICIT Extensions OPTIONAL
                             -- If present, version MUST be v3
        }
*)

(* A predicate says that the length of created TBS (computed
   from `template_len` and `version`) is valid, i.e., less than
   or equal to 2^32 - 6 *)
// let valid_aliasKeyTBS_ingredients
//   (serialNumber: x509_serialNumber_t)
//   (i_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
//   (i_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
//   (i_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
//   (s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
//   (s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
//   (s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
//   (ku: key_usage_payload_t)
//   (version: datatype_of_asn1_type INTEGER)
// = length_of_aliasKeyTBS_payload
//     serialNumber
//     i_common i_org i_country
//     s_common s_org s_country
//     ku version
//   <= asn1_value_length_max_of_type SEQUENCE

let create_aliasKeyTBS_spec
  (crt_version: x509_version_t)
  (serialNumber: x509_serialNumber_t)
  (i_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (i_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (i_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (notBefore: datatype_of_asn1_type Generalized_Time)
  (notAfter : datatype_of_asn1_type Generalized_Time)
  (s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (ku: key_usage_payload_t)
  (keyID: lbytes_pub 20)
  (version: datatype_of_asn1_type INTEGER)
  (fwid: lbytes_sec 32)
  (deviceID_pub: lbytes_pub 32)
  (aliasKey_pub: lbytes_pub 32)
: GTot (aliasKeyTBS_t)
=
(* Create AliasKeyTBS *)
  let deviceID_pub32: B32.lbytes32 32ul = B32.hide deviceID_pub in
  let fwid32        : B32.lbytes32 32ul = B32.hide (declassify_secret_bytes fwid) in
  let aliasKey_pub32: B32.lbytes32 32ul = B32.hide aliasKey_pub in
  let aliasKeyTBS = x509_get_AliasKeyTBS
                                     crt_version
                                     serialNumber
                                     i_common i_org i_country
                                     notBefore notAfter
                                     s_common s_org s_country
                                     ku
                                     (|20ul, B32.hide keyID|)
                                     version
                                     fwid32
                                     deviceID_pub32
                                     aliasKey_pub32 in
  (* Prf *) lemma_serialize_aliasKeyTBS_payload_size aliasKeyTBS;
  (* Prf *) lemma_serialize_aliasKeyTBS_size_exact aliasKeyTBS;

(* return *) aliasKeyTBS

(* Sign and Finalize AliasKey Certificate
  =======================================
  RFC 5280:
   Certificate  ::=  SEQUENCE  {
        tbsCertificate       TBSCertificate,
        signatureAlgorithm   AlgorithmIdentifier,
        signatureValue       BIT STRING  }
*)

(* A predicate says that
   1) the length of TBS is valid as Hacl's HKDF message length
   2) the length of created CRT is valid as our ASN.1 TLV SEQUENCE value length
*)
unfold noextract
let valid_aliasKeyCRT_ingredients
  (tbs_len: asn1_int32)
= // (* implied *) length_of_aliasKeyCRT_payload tbs_len <= max_size_t /\
  length_of_aliasKeyCRT_payload tbs_len <= asn1_value_length_max_of_type SEQUENCE

let sign_and_finalize_aliasKeyCRT_spec
  (deviceID_priv: lbytes_sec 32)
  (aliasKeyTBS_len: size_t
                    { valid_aliasKeyCRT_ingredients aliasKeyTBS_len })
  (aliasKeyTBS_seq: lbytes_pub (v aliasKeyTBS_len))
: GTot (aliasKeyCRT_t aliasKeyTBS_len)
=

(* Classify AliasKeyTBS *)
  let aliasKeyTBS_seq_sec: lbytes_sec (v aliasKeyTBS_len) = classify_public_bytes aliasKeyTBS_seq in

(* Sign AliasKeyTBS *)
  let aliasKeyTBS_sig_sec: lbytes_sec 64 = Spec.Ed25519.sign deviceID_priv aliasKeyTBS_seq_sec in

(* Declassify AliasKeyTBS *)
  let aliasKeyTBS_sig    : lbytes_pub 64 = declassify_secret_bytes aliasKeyTBS_sig_sec in

(* Create AliasKeyCRT with AliasKeyTBS and Signature *)
  let aliasKeyTBS_seq32  : B32.lbytes32 aliasKeyTBS_len = B32.hide aliasKeyTBS_seq in
  let aliasKeyTBS_sig32  : x509_signature_raw_t = B32.hide aliasKeyTBS_sig in
  let aliasKeyCRT: aliasKeyCRT_t aliasKeyTBS_len = x509_get_AliasKeyCRT
                                                             aliasKeyTBS_len
                                                             aliasKeyTBS_seq32
                                                             aliasKeyTBS_sig32 in

(* return *) aliasKeyCRT

let create_deviceIDCRI_spec
  (version: datatype_of_asn1_type INTEGER)
  (s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (ku: key_usage_payload_t
       { valid_deviceIDCRI_ingredients version s_common s_org s_country ku })
  (deviceIDPub: lbytes_pub 32)
: GTot (deviceIDCRI_t)
=
  let deviceIDPub32: B32.lbytes32 32ul = B32.hide deviceIDPub in

  let deviceIDCRI: deviceIDCRI_t = x509_get_deviceIDCRI
                                     version
                                     s_common
                                     s_org
                                     s_country
                                     ku
                                     deviceIDPub32 in
(*return*) deviceIDCRI

let sign_and_finalize_deviceIDCSR_spec
  (deviceID_priv: lbytes_sec 32)
  (deviceIDCRI_len: size_t
                    { valid_deviceIDCSR_ingredients deviceIDCRI_len })
  (deviceIDCRI_seq: lbytes_pub (v deviceIDCRI_len))
: GTot (deviceIDCSR_t deviceIDCRI_len)
=

(* Classify AliasKeyTBS *)
  let deviceIDCRI_seq_sec: lbytes_sec (v deviceIDCRI_len) = classify_public_bytes deviceIDCRI_seq in

(* Sign AliasKeyTBS *)
  let deviceIDCRI_sig_sec: lbytes_sec 64 = Spec.Ed25519.sign deviceID_priv deviceIDCRI_seq_sec in

(* Declassify AliasKeyTBS *)
  let deviceIDCRI_sig    : lbytes_pub 64 = declassify_secret_bytes deviceIDCRI_sig_sec in

(* Create AliasKeyCRT with AliasKeyTBS and Signature *)
  let deviceIDCRI_seq32  : B32.lbytes32 deviceIDCRI_len = B32.hide deviceIDCRI_seq in
  let deviceIDCRI_sig32  : x509_signature_raw_t = B32.hide deviceIDCRI_sig in
  let deviceIDCSR: deviceIDCSR_t deviceIDCRI_len = x509_get_deviceIDCSR
                                                             deviceIDCRI_len
                                                             deviceIDCRI_seq32
                                                             deviceIDCRI_sig32 in

(* return *) deviceIDCSR
