module ASN1.Low.Value.OCTET_STRING

open ASN1.Base
open ASN1.Spec.Value.OCTET_STRING
open ASN1.Low.Base

open FStar.Integers

(* NOTE: Read after `ASN1.Spec.Tag`, `ASN1.Spec.Length` *)

inline_for_extraction
val serialize32_asn1_octet_string_backwards
  (len: asn1_value_int32_of_type OCTET_STRING)
: (serializer32_backwards (serialize_asn1_octet_string (v len)))

// inline_for_extraction
val serialize32_asn1_octet_string_TLV_backwards (_:unit)
: (serializer32_backwards serialize_asn1_octet_string_TLV)
