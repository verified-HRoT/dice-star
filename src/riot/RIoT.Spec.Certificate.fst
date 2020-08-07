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

#set-options "--z3rlimit 32 --fuel 0 --ifuel 0"

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

   In our case:
      TBSCertificate  ::=  SEQUENCE  {
        ----------------
        |              |
        |   Template   |
        |              |
        ----------------
        subjectPublicKeyInfo for AliasKey,
        extensions           for RIoT
        }
   NOTE: The SEQUENCE Tag and Length of TBS is __NOT__ part of the template
   NOTE: Other extensions like Key Usage are __NOT__ included in this version.
*)

(* A predicate says that the length of created TBS (computed
   from `template_len` and `version`) is valid, i.e., less than
   or equal to 2^32 - 6 *)
unfold
let valid_aliasKeyTBS_ingredients
  (template_len: asn1_int32)
  (ku: key_usage_t)
  (version: datatype_of_asn1_type INTEGER)
= length_of_aliasKeyTBS_payload template_len ku version
  <= asn1_value_length_max_of_type SEQUENCE

let create_aliasKeyTBS_spec
  (template_len: asn1_int32)
  (aliasKeyTBS_template: lbytes_pub (v template_len))
  (ku: key_usage_t)
  (version: datatype_of_asn1_type INTEGER
            { length_of_aliasKeyTBS_payload template_len ku version
              <= asn1_value_length_max_of_type SEQUENCE })
  (fwid: lbytes_sec 32)
  (deviceID_pub: lbytes_pub 32)
  (aliasKey_pub: lbytes_pub 32)
: GTot (aliasKeyTBS_t_inbound template_len)
=
(* Create AliasKeyTBS *)
  let aliasKeyTBS_template32: B32.lbytes32 template_len = B32.hide aliasKeyTBS_template in
  let deviceID_pub32: B32.lbytes32 32ul = B32.hide deviceID_pub in
  let fwid32        : B32.lbytes32 32ul = B32.hide (declassify_secret_bytes fwid) in
  let aliasKey_pub32: B32.lbytes32 32ul = B32.hide aliasKey_pub in
  let aliasKeyTBS: aliasKeyTBS_t_inbound template_len = x509_get_AliasKeyTBS
                                                        template_len
                                                        aliasKeyTBS_template32
                                                        ku
                                                        version
                                                        fwid32
                                                        deviceID_pub32
                                                        aliasKey_pub32 in
  (* Prf *) lemma_serialize_aliasKeyTBS_size template_len aliasKeyTBS;
  (* Prf *) lemma_serialize_aliasKeyTBS_sequence_TLV_size_exact template_len aliasKeyTBS;

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
: GTot (aliasKeyCRT_t_inbound aliasKeyTBS_len)
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
  let aliasKeyCRT: aliasKeyCRT_t_inbound aliasKeyTBS_len = x509_get_AliasKeyCRT
                                                             aliasKeyTBS_len
                                                             aliasKeyTBS_seq32
                                                             aliasKeyTBS_sig32 in

(* return *) aliasKeyCRT
