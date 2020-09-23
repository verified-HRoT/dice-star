module ASN1.Low.Value.CharacterString

open ASN1.Low.Base

open ASN1.Base
open ASN1.Spec.Value.CharacterString

include ASN1.Low.Value.StringCombinator
include ASN1.Low.Value.IA5_STRING
include ASN1.Low.Value.PRINTABLE_STRING

open FStar.Integers

noextract inline_for_extraction
val serialize32_asn1_character_string_with_character_bound_backwards
  (t: character_string_type)
  (lb: asn1_value_int32_of_type t)
  (ub: asn1_value_int32_of_type t { lb <= ub })
: serializer32_backwards (serialize_asn1_character_string_with_character_bound t lb ub)
