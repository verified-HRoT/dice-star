module ASN1.Low.Value.PRINTABLE_STRING

open ASN1.Base
open ASN1.Spec.Value.PRINTABLE_STRING
open ASN1.Low.Base

open FStar.Integers

inline_for_extraction noextract
val serialize32_asn1_printable_string_TLV_backwards
: serializer32_backwards (serialize_asn1_printable_string_TLV)

inline_for_extraction noextract
val serialize32_asn1_printable_string_TLV_with_character_bound_backwards
  (lb: asn1_value_int32_of_type PRINTABLE_STRING)
  (ub: asn1_value_int32_of_type PRINTABLE_STRING { lb <= ub })
: serializer32_backwards (serialize_asn1_printable_string_TLV_with_character_bound lb ub)
