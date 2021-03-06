module ASN1.Spec.Value.BIT_STRING

open ASN1.Spec.Base
open LowParse.Spec.SeqBytes.Base

open ASN1.Base
open ASN1.Spec.Tag
open ASN1.Spec.Length

open FStar.Integers

(* NOTE: Read after `ASN1.Spec.Tag`, `ASN1.Spec.Length`, `ASN1.Spec.Value.BIT_STRING` *)

(* NOTE: This module defines:
         1) The ASN1 `BIT_STRING` Value Parser and Serializer
         2) The ASN1 `BIT_STRING` TLV Parser and Serializer

         And each part is organized as:
         1) Aux (ghost) functions with prefix `filter_` to filter out invalid input bytes
         2) Aux (ghost) functions with prefix `synth_` to decode the valid input bytes into our
            representation of BIT_STRING values. These functions are injective.
         3) Aux (ghost) functions with prefix `synth_` and suffix `_inverse` to encode our
            representation of BIT_STRING into bytes. These functions are the inverse of
            corresponding synth functions.
         4) Functions with the prefix `parse_` are parsers constructed using parser combinators and
            aux functions.
         5) Functions with the prefix `serialize_` are serializers constructed using serializer
            combinators and aux functions.
         6) Lemma with suffix `_unfold` reveals the computation of parser/serialzier.
         7) Lemma with suffix `_size` reveals the length of a serialization.
*)

/// TEST
///

// let bs_empty   : datatype_of_asn1_type BIT_STRING = (|1ul, 0ul, B32.empty_bytes |)
// let bs_0_unused: datatype_of_asn1_type BIT_STRING = (|2ul, 0ul, B32.create 1ul 0b1uy|)
// let bs_1_unused: datatype_of_asn1_type BIT_STRING = (|2ul, 1ul, B32.create 1ul 0b10uy|)
// let bs_2_unused: datatype_of_asn1_type BIT_STRING = (|2ul, 2ul, B32.create 1ul 0b100uy|)
// let bs_3_unused: datatype_of_asn1_type BIT_STRING = (|2ul, 3ul, B32.create 1ul 0b1000uy|)
// let bs_4_unused: datatype_of_asn1_type BIT_STRING = (|2ul, 4ul, B32.create 1ul 0b10000uy|)
// let bs_5_unused: datatype_of_asn1_type BIT_STRING = (|2ul, 5ul, B32.create 1ul 0b100000uy|)
// let bs_6_unused: datatype_of_asn1_type BIT_STRING = (|2ul, 6ul, B32.create 1ul 0b1000000uy|)
// let bs_7_unused: datatype_of_asn1_type BIT_STRING = (|2ul, 7ul, B32.create 1ul 0b10000000uy|)

(*
   Len = 1, unused = 0, bytes = []
   Len = 2, unused = x, bytes = [_]
*)

// let (.[]) = B32.index

/// filter valid input bytes
/// 1) if the length of input bytes is 1 (the minimal length), then the first and
///    the only byte, which represents the `unused_bits`, must be 0x00uy
/// 2) otherwise, the `unused_bits` must be in [0, 7] and the last byte's last
/// `unused_bits` bits must be zero.

val filter_asn1_bit_string
  (l: asn1_value_length_of_type BIT_STRING)
  (raw: lbytes l)
: GTot (bool)

/// Decode the valid input bytes into our representation of BIT_STRING,
/// which is a dependent tuple of `total length, unused_bits, octets`
val synth_asn1_bit_string
  (l: asn1_value_length_of_type BIT_STRING)
  (raw: parse_filter_refine (filter_asn1_bit_string l))
: GTot (value: datatype_of_asn1_type BIT_STRING {
               l == v value.bs_len })


/// Encode our representation of BIT_STRING into bytes
val synth_asn1_bit_string_inverse
  (l: asn1_value_length_of_type BIT_STRING)
  (value: datatype_of_asn1_type BIT_STRING {
          l == v value.bs_len })
: GTot (raw: parse_filter_refine (filter_asn1_bit_string l) { value == synth_asn1_bit_string l raw })

inline_for_extraction noextract
let parse_asn1_bit_string_kind (l: asn1_value_length_of_type BIT_STRING) = constant_size_parser_kind l

///
/// ASN1 BIT_STRING Value Parser
///
noextract
val parse_asn1_bit_string
  (l: asn1_value_length_of_type BIT_STRING)
: parser (parse_asn1_bit_string_kind l)
         (value: datatype_of_asn1_type BIT_STRING {
                 l == v value.bs_len })

///
/// ASN1 BIT_STRING Value Serialzier
///
noextract
val serialize_asn1_bit_string
  (l: asn1_value_length_of_type BIT_STRING)
: serializer (parse_asn1_bit_string l)


///
/// Lemmas
///

/// Reveal the computation of parse
val lemma_parse_asn1_bit_string_unfold
  (l: asn1_value_length_of_type BIT_STRING)
  (input: bytes)
: Lemma (
  parse (parse_asn1_bit_string l) input ==
 (match parse (parse_seq_flbytes l) input with
  | None -> None
  | Some (raw, consumed) -> ( if filter_asn1_bit_string l raw then
                              ( Some (synth_asn1_bit_string l raw, consumed) )
                              else
                              ( None )) )
)

/// Reveal the computation of serialize
val lemma_serialize_asn1_bit_string_unfold
  (l: asn1_value_length_of_type BIT_STRING)
  (value: datatype_of_asn1_type BIT_STRING {
                 l == v value.bs_len })
: Lemma (
  serialize (serialize_asn1_bit_string l) value ==
  serialize (serialize_seq_flbytes l) (synth_asn1_bit_string_inverse l value))

/// Reveal the length of a serialzation
val lemma_serialize_asn1_bit_string_size
  (l: asn1_value_length_of_type BIT_STRING)
  (value: datatype_of_asn1_type BIT_STRING {
                 l == v value.bs_len })
: Lemma (
  Seq.length (serialize (serialize_asn1_bit_string l) value) == l)

///////////////////////////////////////////////////////////
//// ASN1 `BIT_STRING` TLV Parser and Serializer
///////////////////////////////////////////////////////////

/// parser tag for the `tagged_union` combinators
noextract
val parser_tag_of_bit_string
  (x: datatype_of_asn1_type BIT_STRING)
: GTot (the_asn1_tag BIT_STRING & asn1_value_int32_of_type BIT_STRING)

///
/// A pair of aux parser/serializer, which explicitly coerce the `BIT_STRING` value
/// between the subtype used by `BIT_STRING` value parser/serialzier and `BIT_STRING`
/// TLV parser/serializer.
///
/// NOTE: I found that have this aux parser explicitly defined will make the prove of
///       `_unfold` lemmas simpler.
///

/// Convert an `BIT_STRING` value from the subtype used by its value parser to the subtype
/// used by its TLV parser/serializer
/// (value : subtype_{value}) <: subtype_{TLV}
noextract
val synth_asn1_bit_string_V
  (tag: (the_asn1_tag BIT_STRING & asn1_value_int32_of_type BIT_STRING))
  (value: datatype_of_asn1_type BIT_STRING {
                 v (snd tag) == v value.bs_len })
: GTot (refine_with_tag parser_tag_of_bit_string tag)

/// Convert an `BIT_STRING` value from the subtype used by its TLV parser to the subtype
/// used by its value parser/serializer
/// (value : subtype_{TLV}) <: subtype_{value}

val synth_asn1_bit_string_V_inverse
  (tag: (the_asn1_tag BIT_STRING & asn1_value_int32_of_type BIT_STRING))
  (value': refine_with_tag parser_tag_of_bit_string tag)
: GTot (value: datatype_of_asn1_type BIT_STRING {
                 v (snd tag) == v value.bs_len /\
                 value' == synth_asn1_bit_string_V tag value })

///
/// Aux parser
///
noextract
val parse_asn1_bit_string_V
  (tag: (the_asn1_tag BIT_STRING & asn1_value_int32_of_type BIT_STRING))
: parser (weak_kind_of_type BIT_STRING) (refine_with_tag parser_tag_of_bit_string tag)

///
/// Aux serializer
///
noextract
val serialize_asn1_bit_string_V
  (tag: (the_asn1_tag BIT_STRING & asn1_value_int32_of_type BIT_STRING))
: serializer (parse_asn1_bit_string_V tag)

///
/// Lemmas
///

/// Reveal the computation of parse
val lemma_parse_asn1_bit_string_V_unfold
  (tag: (the_asn1_tag BIT_STRING & asn1_value_int32_of_type BIT_STRING))
  (input: bytes)
: Lemma (
  parse (parse_asn1_bit_string_V tag) input ==
 (match parse (parse_asn1_bit_string (v (snd tag))) input with
  | None -> None
  | Some (value, consumed) ->  Some (synth_asn1_bit_string_V tag value, consumed)))


inline_for_extraction noextract
let parse_asn1_bit_string_TLV_kind
: parser_kind
= parse_asn1_tag_kind
  `and_then_kind`
  parse_asn1_length_kind_of_type BIT_STRING
  `and_then_kind`
  weak_kind_of_type BIT_STRING

///
/// ASN1 `BIT_STRING` TLV Parser
///

noextract
val parse_asn1_bit_string_TLV
: parser parse_asn1_bit_string_TLV_kind (datatype_of_asn1_type BIT_STRING)

///
/// ASN1 `BIT_STRING` TLV Serializer
///

noextract
val serialize_asn1_bit_string_TLV
: serializer parse_asn1_bit_string_TLV

///
/// Lemmas
///

/// Reveal the computation of parse

val lemma_parse_asn1_bit_string_TLV_unfold
  (input: bytes)
: Lemma (
  parse parse_asn1_bit_string_TLV input ==
 (match parse (parse_asn1_tag_of_type BIT_STRING) input with
  | None -> None
  | Some (tag, consumed_tag) ->
    (let input_LV = Seq.slice input consumed_tag (Seq.length input) in
     match parse (parse_asn1_length_of_type BIT_STRING) input_LV with
     | None -> None
     | Some (len, consumed_len) ->
       (let input_V = Seq.slice input_LV consumed_len (Seq.length input_LV) in
        match parse (parse_asn1_bit_string (v len)) input_V with
        | None -> None
        | Some (value, consumed_value) ->
               Some ((synth_asn1_bit_string_V (tag, len) value),
                     (consumed_tag + consumed_len + consumed_value <: consumed_length input)))))
)

/// Reveal the computation of serialize

val lemma_serialize_asn1_bit_string_TLV_unfold
  (value: datatype_of_asn1_type BIT_STRING)
: Lemma (
  serialize serialize_asn1_bit_string_TLV value ==
  serialize (serialize_asn1_tag_of_type BIT_STRING) BIT_STRING
  `Seq.append`
  serialize (serialize_asn1_length_of_type BIT_STRING) value.bs_len
  `Seq.append`
  serialize (serialize_asn1_bit_string (v value.bs_len)) value
)

/// Reveal the size of a serialzation

val lemma_serialize_asn1_bit_string_TLV_size
  (value: datatype_of_asn1_type BIT_STRING)
: Lemma (
  Seq.length (serialize serialize_asn1_bit_string_TLV value) ==
  1 + length_of_asn1_length value.bs_len + v value.bs_len)
