module ASN1.Low.Value.CharacterString

open ASN1.Low.Base
open LowParse.Low.Bytes

open ASN1.Base
open ASN1.Low.Tag
open ASN1.Low.Length
open ASN1.Spec.Value.CharacterString
include ASN1.Low.Value.StringCombinator
include ASN1.Low.Value.IA5_STRING
include ASN1.Low.Value.PRINTABLE_STRING

open FStar.Integers

module B32 = FStar.Bytes

let serialize32_asn1_character_string_with_character_bound_backwards
  (t: character_string_type)
  (lb: asn1_value_int32_of_type t)
  (ub: asn1_value_int32_of_type t { lb <= ub })
: serializer32_backwards (serialize_asn1_character_string_with_character_bound t lb ub)
= match t with
  | IA5_STRING -> assert_norm (count_ia5_character == count_character IA5_STRING);
                  serialize32_asn1_ia5_string_TLV_with_character_bound_backwards lb ub
  | PRINTABLE_STRING
               -> assert_norm (count_printable_character == count_character PRINTABLE_STRING);
                  serialize32_asn1_printable_string_TLV_with_character_bound_backwards lb ub
