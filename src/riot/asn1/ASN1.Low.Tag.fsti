module ASN1.Low.Tag
///
/// ASN.1 Low
///

open ASN1.Base
open ASN1.Spec.Tag
open ASN1.Low.Base


/// Backwards low-level serializer for asn1 tags

inline_for_extraction
val serialize32_asn1_tag_backwards (_:unit)
: (serializer32_backwards serialize_asn1_tag)


/// Backwards low-level serializer for a specific asn1 tag

inline_for_extraction noextract
val serialize32_asn1_tag_of_type_backwards
  (_a: asn1_tag_t)
: (serializer32_backwards (serialize_asn1_tag_of_type _a))
