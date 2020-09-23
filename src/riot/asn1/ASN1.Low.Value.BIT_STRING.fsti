module ASN1.Low.Value.BIT_STRING

open ASN1.Base
open ASN1.Spec.Value.BIT_STRING

open ASN1.Low.Base

open FStar.Integers

(* NOTE: Read after `ASN1.Spec.Tag`, `ASN1.Spec.Length`, `ASN1.Spec.Value.OCTET_STRING` *)

inline_for_extraction
val serialize32_asn1_bit_string_backwards
  (len: asn1_value_int32_of_type BIT_STRING)
: (serializer32_backwards (serialize_asn1_bit_string (v len)))

// inline_for_extraction
val serialize32_asn1_bit_string_TLV_backwards (_:unit)
: (serializer32_backwards (serialize_asn1_bit_string_TLV))
