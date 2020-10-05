module ASN1.Low.Value.OID

open ASN1.Base
open ASN1.Spec.Value.OID
open ASN1.Low.Base

open FStar.Integers

inline_for_extraction noextract unfold
[@@ "opaque_to_smt"]
let len_of_oid
  (oid: oid_t)
: Tot (len: asn1_value_int32_of_type OID
      { v len == length_of_oid oid })
= match oid with
  | OID_RIOT                     -> 9ul
  | OID_AT_CN                    -> 3ul
  | OID_AT_COUNTRY               -> 3ul
  | OID_AT_ORGANIZATION          -> 3ul
  | OID_CLIENT_AUTH              -> 7ul
  | OID_AUTHORITY_KEY_IDENTIFIER -> 3ul
  | OID_KEY_USAGE                -> 3ul
  | OID_EXTENDED_KEY_USAGE       -> 3ul
  | OID_BASIC_CONSTRAINTS        -> 3ul
  | OID_DIGEST_SHA256            -> 9ul
  | OID_EC_ALG_UNRESTRICTED      -> 5ul
  | OID_EC_GRP_SECP256R1         -> 6ul
  | OID_ED25519                  -> 3ul
  | OID_X25519                   -> 3ul
  | OID_PKCS9_CSR_EXT_REQ        -> 9ul

inline_for_extraction
val serialize32_asn1_oid_backwards
  (len: asn1_value_int32_of_type OID)
: Tot (serializer32_backwards (serialize_asn1_oid (v len)))

val serialize32_asn1_oid_TLV_backwards (_: unit)
: Tot (serializer32_backwards serialize_asn1_oid_TLV)

noextract inline_for_extraction
val serialize32_asn1_oid_TLV_of_backwards
  (oid: datatype_of_asn1_type OID)
: serializer32_backwards (serialize_asn1_oid_TLV_of oid)

inline_for_extraction
val serialize32_envelop_OID_with_backwards
  (oid: datatype_of_asn1_type OID)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (#s: serializer p)
  (s32: serializer32_backwards s)
: serializer32_backwards (serialize_envelop_OID_with oid s)
