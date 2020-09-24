module ASN1.Low.Value.OID

open ASN1.Base
open ASN1.Spec.Value.OID
open ASN1.Low.Base
open LowParse.Low.Bytes

open FStar.Integers

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module MB = LowStar.Monotonic.Buffer
module B = LowStar.Buffer
module Cast = FStar.Int.Cast

module B32 = FStar.Bytes

module IB = LowStar.ImmutableBuffer
module CB = LowStar.ConstBuffer

module G = FStar.Ghost

noextract
val len_of_oid
  (oid: oid_t)
: Tot (len: asn1_value_int32_of_type OID
      { v len == length_of_oid oid })

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
