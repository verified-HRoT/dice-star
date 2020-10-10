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
val serialize32_asn1_octet_string_TLV_with_tag_backwards (a: asn1_tag_t)
: (serializer32_backwards (serialize_asn1_octet_string_TLV_with_tag a))

noextract inline_for_extraction
let serialize32_asn1_octet_string_TLV_backwards ()
: serializer32_backwards (serialize_asn1_octet_string_TLV)
= serialize32_asn1_octet_string_TLV_with_tag_backwards OCTET_STRING
