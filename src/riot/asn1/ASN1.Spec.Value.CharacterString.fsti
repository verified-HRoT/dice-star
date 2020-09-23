module ASN1.Spec.Value.CharacterString

open ASN1.Spec.Base

open ASN1.Base

include ASN1.Spec.Value.StringCombinator
include ASN1.Spec.Value.IA5_STRING
include ASN1.Spec.Value.PRINTABLE_STRING

open FStar.Integers

noextract inline_for_extraction
val count_character
  (t: character_string_type)
  (x: datatype_of_asn1_type t)
: asn1_int32

val parse_asn1_character_string
  (t: character_string_type)
: parser (parse_asn1_string_TLV_kind t) (datatype_of_asn1_type t)

val serialize_asn1_character_string
  (t: character_string_type)
: serializer (parse_asn1_character_string t)

val parse_asn1_character_string_with_character_bound
  (t: character_string_type)
  (lb: asn1_value_int32_of_type t)
  (ub: asn1_value_int32_of_type t { lb <= ub })
: parser (parse_asn1_string_TLV_kind t) (asn1_string_with_character_bound_t t (count_character t) lb ub)

val serialize_asn1_character_string_with_character_bound
  (t: character_string_type)
  (lb: asn1_value_int32_of_type t)
  (ub: asn1_value_int32_of_type t { lb <= ub })
: serializer (parse_asn1_character_string_with_character_bound t lb ub)

val lemma_serialize_character_string_unfold
  (t: character_string_type)
  // (lb: asn1_value_int32_of_type t)
  // (ub: asn1_value_int32_of_type t { lb <= ub })
  // (x: asn1_string_with_character_bound_t t (count_character t) lb ub)
  (x: datatype_of_asn1_type t)
: Lemma (
    match t with
    | IA5_STRING -> predicate_serialize_asn1_string_TLV_unfold
                     (IA5_STRING)
                     (dfst)
                     (filter_asn1_ia5_string)
                     (synth_asn1_ia5_string)
                     (synth_asn1_ia5_string_inverse)
                     ()
                     (x)
    | PRINTABLE_STRING
                 -> predicate_serialize_asn1_string_TLV_unfold
                     (PRINTABLE_STRING)
                     (dfst)
                     (filter_asn1_printable_string)
                     (synth_asn1_printable_string)
                     (synth_asn1_printable_string_inverse)
                     ()
                     (x))

val lemma_serialize_character_string_size
  (t: character_string_type)
  // (lb: asn1_value_int32_of_type t)
  // (ub: asn1_value_int32_of_type t { lb <= ub })
  // (x: asn1_string_with_character_bound_t t (count_character t) lb ub)
  (x: datatype_of_asn1_type t)
: Lemma (
    match t with
    | IA5_STRING -> predicate_serialize_asn1_string_TLV_size
                     (IA5_STRING)
                     (dfst)
                     (filter_asn1_ia5_string)
                     (synth_asn1_ia5_string)
                     (synth_asn1_ia5_string_inverse)
                     ()
                     (x)
    | PRINTABLE_STRING
                 -> predicate_serialize_asn1_string_TLV_size
                     (PRINTABLE_STRING)
                     (dfst)
                     (filter_asn1_printable_string)
                     (synth_asn1_printable_string)
                     (synth_asn1_printable_string_inverse)
                     ()
                     (x))
