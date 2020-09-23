module ASN1.Low.Value.BOOLEAN
///
/// ASN.1 Low
///

open ASN1.Spec.Value.BOOLEAN
open ASN1.Low.Base

(* NOTE: Read after `ASN1.Spec.Tag`, `ASN1.Spec.Length` *)


///
/// Backwards low-level serializer for ASN1 BOOLEAN values
///
inline_for_extraction
val serialize32_asn1_boolean_backwards (_:unit)
: (serializer32_backwards serialize_asn1_boolean)

///
/// Low-level backwards serializer for ASN1 BOOLEAN TLV
///

///
/// Backwards low-level serializer which takes a BOOLEAN value and serializes its TLV tuple.
///
// inline_for_extraction
val serialize32_asn1_boolean_TLV_backwards (_:unit)
: (serializer32_backwards serialize_asn1_boolean_TLV)

val serialize32_asn1_boolean_TLV_true_backwards (_:unit)
: (serializer32_backwards serialize_asn1_boolean_TLV_true)

val serialize32_asn1_boolean_TLV_false_backwards (_:unit)
: (serializer32_backwards serialize_asn1_boolean_TLV_false)
