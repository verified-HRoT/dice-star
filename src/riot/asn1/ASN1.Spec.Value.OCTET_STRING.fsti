module ASN1.Spec.Value.OCTET_STRING

open ASN1.Spec.Base
open LowParse.Spec.Bytes

open ASN1.Base
open ASN1.Spec.Tag
open ASN1.Spec.Length

open FStar.Integers

module B32 = FStar.Bytes

(* NOTE: Read after `ASN1.Spec.Tag`, `ASN1.Spec.Length`, `ASN1.Spec.Value.OCTET_STRING` *)

(* NOTE: This module defines:
         1) The ASN1 `OCTET_STRING` Value Parser and Serializer
         2) The ASN1 `OCTET_STRING` TLV Parser and Serializer

         And each part is organized as:
         1) Aux (ghost) functions with prefix `filter_` to filter out invalid input bytes
         2) Aux (ghost) functions with prefix `synth_` to decode the valid input bytes into our
            representation of OCTET_STRING values. These functions are injective.
         3) Aux (ghost) functions with prefix `synth_` and suffix `_inverse` to encode our
            representation of OCTET_STRING into bytes. These functions are the inverse of
            corresponding synth functions.
         4) Functions with the prefix `parse_` are parsers constructed using parser combinators and
            aux functions.
         5) Functions with the prefix `serialize_` are serializers constructed using serializer
            combinators and aux functions.
         6) Lemma with suffix `_unfold` reveals the computation of parser/serialzier.
         7) Lemma with suffix `_size` reveals the length of a serialization.
*)

///////////////////////////////////////////////////////////
//// ASN1 `OCTET_STRING` Value Parser and Serializer
//////////////////////////////////////////////////////////

/// Decodes input bytes into our representation of a OCTET_STRING value
noextract
val synth_asn1_octet_string
  (l: asn1_value_length_of_type OCTET_STRING)
  (s32: B32.lbytes l)
: GTot (value: datatype_of_asn1_type OCTET_STRING{v (dfst value) == l})


/// Encodes our representation of a OCTET_STRING into bytes
noextract
val synth_asn1_octet_string_inverse
  (l: asn1_value_length_of_type OCTET_STRING)
  (value: datatype_of_asn1_type OCTET_STRING{v (dfst value) == l})
: GTot (s32: B32.lbytes l{ value == synth_asn1_octet_string l s32 })

inline_for_extraction noextract
let parse_asn1_octet_string_kind (l: asn1_value_length_of_type OCTET_STRING) = total_constant_size_parser_kind l

///
/// Parser
///
noextract
val parse_asn1_octet_string
  (l: asn1_value_length_of_type OCTET_STRING)
: parser (parse_asn1_octet_string_kind l) (x: datatype_of_asn1_type OCTET_STRING{v (dfst x) == l})

///
/// Serializer
///
noextract
val serialize_asn1_octet_string
  (l: asn1_value_length_of_type OCTET_STRING)
: serializer (parse_asn1_octet_string l)


///
/// Lemmas
///

/// Reveal the computation of parse
val lemma_parse_asn1_octet_string_unfold
  (l: asn1_value_length_of_type OCTET_STRING)
  (input: bytes)
: Lemma (
  parse (parse_asn1_octet_string l) input ==
 (match parse (parse_flbytes l) input with
  | None -> None
  | Some (ls, consumed) -> Some (synth_asn1_octet_string l ls, consumed)))

/// Reveal the computation of serialize
val lemma_serialize_asn1_octet_string_unfold
  (l: asn1_value_length_of_type OCTET_STRING)
  (value: datatype_of_asn1_type OCTET_STRING{v (dfst value) == l})
: Lemma (
  serialize (serialize_asn1_octet_string l) value ==
  serialize (serialize_flbytes l) (synth_asn1_octet_string_inverse l value))

/// Reveal the length of a serialzation
val lemma_serialize_asn1_octet_string_size
  (l: asn1_value_length_of_type OCTET_STRING)
  (value: datatype_of_asn1_type OCTET_STRING{v (dfst value) == l})
: Lemma (
  Seq.length (serialize (serialize_asn1_octet_string l) value) == l)


///////////////////////////////////////////////////////////
//// ASN1 `OCTET_STRING` TLV Parser and Serializer
///////////////////////////////////////////////////////////

/// parser tag for the `tagged_union` combinators

noextract
val parser_tag_of_octet_string
  (x: datatype_of_asn1_type OCTET_STRING)
: GTot (the_asn1_tag OCTET_STRING & asn1_value_int32_of_type OCTET_STRING)

inline_for_extraction noextract
let parse_asn1_octet_string_TLV_kind
: parser_kind
= parse_asn1_tag_kind
  `and_then_kind`
  parse_asn1_length_kind_of_type OCTET_STRING
  `and_then_kind`
  weak_kind_of_type OCTET_STRING

///
/// A pair of aux parser/serializer, which explicitly coerce the `OCTET_STRING` value
/// between the subtype used by `OCTET_STRING` value parser/serialzier and `OCTET_STRING`
/// TLV parser/serializer.
///
/// NOTE: I found that have this aux parser explicitly defined will make the prove of
///       `_unfold` lemmas simpler.
///

/// Convert an `OCTET_STRING` value from the subtype used by its value parser to the subtype
/// used by its TLV parser/serializer
/// (value : subtype_{value}) <: subtype_{TLV}

noextract
val synth_asn1_octet_string_V
  (tag: (the_asn1_tag OCTET_STRING & asn1_value_int32_of_type OCTET_STRING))
  (value: datatype_of_asn1_type OCTET_STRING { v (dfst value) == v (snd tag) })
: GTot (refine_with_tag parser_tag_of_octet_string tag)

/// Convert an `OCTET_STRING` value from the subtype used by its TLV parser to the subtype
/// used by its value parser/serializer
/// (value : subtype_{TLV}) <: subtype_{value}

noextract
val synth_asn1_octet_string_V_inverse
  (tag: (the_asn1_tag OCTET_STRING & asn1_value_int32_of_type OCTET_STRING))
  (value': refine_with_tag parser_tag_of_octet_string tag)
: GTot (value: datatype_of_asn1_type OCTET_STRING { v (dfst value) == v (snd tag) /\ value' == synth_asn1_octet_string_V tag value})


///
/// Aux parser
///

noextract
val parse_asn1_octet_string_V
  (tag: (the_asn1_tag OCTET_STRING & asn1_value_int32_of_type OCTET_STRING))
: parser (weak_kind_of_type OCTET_STRING) (refine_with_tag parser_tag_of_octet_string tag)

///
/// Aux serializer
///

noextract
val serialize_asn1_octet_string_V
  (tag: (the_asn1_tag OCTET_STRING & asn1_value_int32_of_type OCTET_STRING))
: serializer (parse_asn1_octet_string_V tag)

///
/// Lemmas
///

/// Reveal the computation of parse

val lemma_parse_asn1_octet_string_V_unfold
  (tag: (the_asn1_tag OCTET_STRING & asn1_value_int32_of_type OCTET_STRING))
  (input: bytes)
: Lemma (
  parse (parse_asn1_octet_string_V tag) input ==
 (match parse (parse_asn1_octet_string (v (snd tag))) input with
  | None -> None
  | Some (value, consumed) ->  Some (synth_asn1_octet_string_V tag value, consumed)))


//////////////////////////////////////////////////////////
///
/// ASN1 `OCTET_STRING` TLV Parser
///
noextract
val parse_asn1_octet_string_TLV
: parser parse_asn1_octet_string_TLV_kind (datatype_of_asn1_type OCTET_STRING)

///
/// Serializer
///
noextract
val serialize_asn1_octet_string_TLV
: serializer parse_asn1_octet_string_TLV

///
/// Lemmas
///

/// Reveal the computation of serialize

val lemma_serialize_asn1_octet_string_TLV_unfold
  (value: datatype_of_asn1_type OCTET_STRING)
: Lemma (
  serialize serialize_asn1_octet_string_TLV value ==
  serialize (serialize_asn1_tag_of_type OCTET_STRING) OCTET_STRING
  `Seq.append`
  serialize (serialize_asn1_length_of_type OCTET_STRING) (dfst value)
  `Seq.append`
  serialize (serialize_asn1_octet_string (v (dfst value))) value
)

/// Reveal the size of a serialzation

val lemma_serialize_asn1_octet_string_TLV_size
  (value: datatype_of_asn1_type OCTET_STRING)
: Lemma (
  Seq.length (serialize serialize_asn1_octet_string_TLV value) ==
  1 + length_of_asn1_length (dfst value) + B32.length (dsnd value)
)
