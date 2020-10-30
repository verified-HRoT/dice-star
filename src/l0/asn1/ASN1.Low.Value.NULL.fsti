module ASN1.Low.Value.NULL

open ASN1.Spec.Value.NULL
open ASN1.Low.Base

(* NOTE: Read after `ASN1.Spec.Tag`, `ASN1.Spec.Length` *)

inline_for_extraction
val serialize32_asn1_ASN1_NULL_backwards (_:unit)
: (serializer32_backwards serialize_asn1_ASN1_NULL)

// inline_for_extraction
val serialize32_asn1_ASN1_NULL_TLV_backwards (_:unit)
: (serializer32_backwards serialize_asn1_ASN1_NULL_TLV)
