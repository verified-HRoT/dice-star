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
: GTot (value: datatype_of_asn1_type OCTET_STRING{v (value.len) == l})


/// Encodes our representation of a OCTET_STRING into bytes
noextract
val synth_asn1_octet_string_inverse
  (l: asn1_value_length_of_type OCTET_STRING)
  (value: datatype_of_asn1_type OCTET_STRING{v (value.len) == l})
: GTot (s32: B32.lbytes l{ value == synth_asn1_octet_string l s32 })

inline_for_extraction noextract
let parse_asn1_octet_string_kind (l: asn1_value_length_of_type OCTET_STRING) = total_constant_size_parser_kind l

///
/// Parser
///
noextract
val parse_asn1_octet_string
  (l: asn1_value_length_of_type OCTET_STRING)
: parser (parse_asn1_octet_string_kind l) (x: datatype_of_asn1_type OCTET_STRING{v (x.len) == l})

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
  (value: datatype_of_asn1_type OCTET_STRING{v (value.len) == l})
: Lemma (
  serialize (serialize_asn1_octet_string l) value ==
  serialize (serialize_flbytes l) (synth_asn1_octet_string_inverse l value))

/// Reveal the length of a serialzation
val lemma_serialize_asn1_octet_string_size
  (l: asn1_value_length_of_type OCTET_STRING)
  (value: datatype_of_asn1_type OCTET_STRING{v (value.len) == l})
: Lemma (
  Seq.length (serialize (serialize_asn1_octet_string l) value) == l)


///////////////////////////////////////////////////////////
//// ASN1 `OCTET_STRING` TLV Parser and Serializer
///////////////////////////////////////////////////////////

inline_for_extraction noextract
let parse_asn1_octet_string_TLV_kind
: parser_kind
= parse_asn1_tag_kind
  `and_then_kind`
  parse_asn1_length_kind_of_type OCTET_STRING
  `and_then_kind`
  weak_kind_of_type OCTET_STRING

//////////////////////////////////////////////////////////
///
/// ASN1 `OCTET_STRING` TLV Parser
///
noextract
val parse_asn1_octet_string_TLV_with_tag (a: asn1_tag_t)
: parser parse_asn1_octet_string_TLV_kind (datatype_of_asn1_type OCTET_STRING)

///
/// Serializer
///
noextract
val serialize_asn1_octet_string_TLV_with_tag (a: asn1_tag_t)
: serializer (parse_asn1_octet_string_TLV_with_tag a)

///
/// Lemmas
///

/// Reveal the computation of serialize

val lemma_serialize_asn1_octet_string_TLV_with_tag_unfold
  (a: asn1_tag_t)
  (value: datatype_of_asn1_type OCTET_STRING)
: Lemma (
  serialize (serialize_asn1_octet_string_TLV_with_tag a) value ==
  serialize (serialize_asn1_tag_of_type a) a
  `Seq.append`
  serialize (serialize_asn1_length_of_type OCTET_STRING) (value.len)
  `Seq.append`
  serialize (serialize_asn1_octet_string (v (value.len))) value
)

/// Reveal the size of a serialzation

val lemma_serialize_asn1_octet_string_TLV_with_tag_size
  (a: asn1_tag_t)
  (value: datatype_of_asn1_type OCTET_STRING)
: Lemma (
  Seq.length (serialize (serialize_asn1_octet_string_TLV_with_tag a) value) ==
  1 + length_of_asn1_length (value.len) + B32.length (value.s)
)


noextract inline_for_extraction unfold
let parse_asn1_octet_string_TLV = parse_asn1_octet_string_TLV_with_tag OCTET_STRING

noextract inline_for_extraction unfold
let serialize_asn1_octet_string_TLV = serialize_asn1_octet_string_TLV_with_tag OCTET_STRING

unfold
let lemma_serialize_asn1_octet_string_TLV_unfold = lemma_serialize_asn1_octet_string_TLV_with_tag_unfold OCTET_STRING

unfold
let lemma_serialize_asn1_octet_string_TLV_size = lemma_serialize_asn1_octet_string_TLV_with_tag_size OCTET_STRING
