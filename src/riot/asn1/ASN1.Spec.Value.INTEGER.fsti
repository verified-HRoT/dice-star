module ASN1.Spec.Value.INTEGER

open ASN1.Spec.Base
open LowParse.Spec.SeqBytes.Base

open ASN1.Base
open ASN1.Spec.Tag
open ASN1.Spec.Length

open FStar.Integers

(* NOTE: Read after `ASN1.Spec.Tag`, `ASN1.Spec.Length` *)

(* NOTE: This module defines:
         1) The ASN1 `INTEGER` Value Parser and Serializer
         2) The ASN1 `INTEGER` TLV Parser and Serializer

         And each part is organized as:
         1) Aux (ghost) functions with prefix `filter_` to filter out invalid input bytes
         2) Aux (ghost) functions with prefix `synth_` to decode the valid input bytes into our
            representation of INTEGER values. These functions are injective.
         3) Aux (ghost) functions with prefix `synth_` and suffix `_inverse` to encode our
            representation of INTEGER into bytes. These functions are the inverse of
            corresponding synth functions.
         4) Functions with the prefix `parse_` are parsers constructed using parser combinators and
            aux functions.
         5) Functions with the prefix `serialize_` are serializers constructed using serializer
            combinators and aux functions.
         6) Lemma with suffix `_unfold` reveals the computation of parser/serialzier.
         7) Lemma with suffix `_size` reveals the length of a serialization.
*)

(*
NOTE: 1. Negative: `**p & 0x80 == 0`, reject
      2. Zero    : as `[0x02; 0x01; 0x00]` for INTEGER or `[0x0A; 0x01; 0x00]` fir ENUMERATED tags
      3. Positive: if the most significant bit of a positive integer is `1`, then add a leading zero.

NOTE: MbedTLS's implementation seems allow arbitrary leading zeros. We only allow one leading zero for now.
NOTE: We only allow at most 4-byte positive integers ([0, 0x7FFFFFFF]). If an integer is encoded into 5 bytes with a leading
      zero, then it must be a negative integer.
*)

//////////////////////////////////////////////////////////////////////
////       ASN1 `INTEGER` Value Parser/Serializer
//////////////////////////////////////////////////////////////////////

/// filters the valid input bytes accoring to the encoding rule
/// 1. valid length of input bytes is [1, 4]
/// 2. only positive integers, whether
///    a) the most significant bit is `0` (the first byte is less than 0x80uy/0b10000000uy), or
///    b) the first byte is a leading zero 0x00uy and the second byte's most significant bit is `1`
///       (the second byte is greater then or equal to 0x80uy/0b10000000uy)
noextract
val filter_asn1_integer
  (l: asn1_value_length_of_type INTEGER) (* 1 <= l <= 4*)
  (s: lbytes l)
: GTot (bool)

/// Length computation function/specification for a `INTEGER` value's serialization
noextract
val length_of_asn1_integer
  (value: datatype_of_asn1_type INTEGER)
: GTot (asn1_value_length_of_type INTEGER)

(* NOTE: Why this function signature will not pass type check when
         `datatype_of_asn1_type` is marked as `unfold`? *)
(* NOTE: Why I must explicitly provide #(Signed W32) everywhere? *)

/// Decode the valid input bytes to our represenation of ASN1 `INTEGER` value,
/// which is a _positive_ _signed_ 32-bit integer
/// 1) If the first byte is less then 0x80uy, then just decode it as an integer (in Big-Endian)
/// 2) If the first byte is a leading zero, then truncate it and decode the rest bytes as an
///    integer (in Big-Endian)
#restart-solver
noextract
val synth_asn1_integer
  (l: asn1_value_length_of_type INTEGER)
  (s: parse_filter_refine (filter_asn1_integer l))
: GTot (value: datatype_of_asn1_type INTEGER { l == length_of_asn1_integer value })


/// Encode an integre accoding to the encoding rule
noextract
val synth_asn1_integer_inverse
  (l: asn1_value_length_of_type INTEGER)
  (value: datatype_of_asn1_type INTEGER { l == length_of_asn1_integer value } )
: GTot (s: parse_filter_refine (filter_asn1_integer l) { value == synth_asn1_integer l s })

/// Prove that the our decoding function is injective when there is a leading zero
/// in the input bytes

val synth_asn1_integer_injective_with_leading_zero
  (l: asn1_value_length_of_type INTEGER)
  (s1 s2: parse_filter_refine (filter_asn1_integer l))
: Lemma
  (requires synth_asn1_integer l s1 == synth_asn1_integer l s2 /\
            s1.[0] == 0x00uy)
  (ensures  s2.[0] == 0x00uy /\ s1 `Seq.equal` s2)

/// Prove that the our decoding function is injective when there is no leading zero
/// in the input bytes
val synth_asn1_integer_injective_without_leading_zero
  (l: asn1_value_length_of_type INTEGER)
  (s1 s2: parse_filter_refine (filter_asn1_integer l))
: Lemma
  (requires synth_asn1_integer l s1 == synth_asn1_integer l s2 /\
            s1.[0] <> 0x00uy /\ s2.[0] <> 0x00uy)
  (ensures  s1 `Seq.equal` s2)

/// Prove that the our decoding function is injective
val synth_asn1_integer_injective'
  (l: asn1_value_length_of_type INTEGER)
  (s1 s2: parse_filter_refine (filter_asn1_integer l))
: Lemma
  (requires synth_asn1_integer l s1 == synth_asn1_integer l s2)
  (ensures s1 `Seq.equal` s2)

val synth_asn1_integer_injective
  (l: asn1_value_length_of_type INTEGER)
: Lemma (synth_injective (synth_asn1_integer l))

inline_for_extraction noextract
let parse_asn1_integer_kind (l: asn1_value_length_of_type INTEGER) = constant_size_parser_kind l


///
/// Parser
///
noextract
val parse_asn1_integer
  (l: asn1_value_length_of_type INTEGER)
: parser (parse_asn1_integer_kind l)
         (value: datatype_of_asn1_type INTEGER { l == length_of_asn1_integer value })

///
/// Serializer
///
noextract
val serialize_asn1_integer
  (l: asn1_value_length_of_type INTEGER)
: serializer (parse_asn1_integer l)

///
/// Lemmas
///

/// Reveal the computation of parse
val lemma_parse_asn1_integer_unfold
  (l: asn1_value_length_of_type INTEGER)
  (input: bytes)
: Lemma (
  parse_asn1_integer l input ==
 (match parse (parse_seq_flbytes l) input with
  | None -> None
  | Some (s, consumed) -> if filter_asn1_integer l s then
                          ( Some (synth_asn1_integer l s, consumed) )
                          else
                          ( None )))

/// Reveal the computaion of serialize
val lemma_serialize_asn1_integer_unfold
  (l: asn1_value_length_of_type INTEGER)
  (value: datatype_of_asn1_type INTEGER { l == length_of_asn1_integer value })
: Lemma (
  serialize (serialize_asn1_integer l) value ==
  synth_asn1_integer_inverse l value)

/// Reveal the size of a serialization
val lemma_serialize_asn1_integer_size
  (l: asn1_value_length_of_type INTEGER)
  (value: datatype_of_asn1_type INTEGER { l == length_of_asn1_integer value })
: Lemma (
  Seq.length (serialize (serialize_asn1_integer l) value) ==
  length_of_asn1_integer value)

///////////////////////////////////////////////////////////
//// ASN1 aux `INTEGER` TLV Parser and Serializer
///////////////////////////////////////////////////////////

/// parser tag for the `tagged_union` combinators
noextract
val parser_tag_of_asn1_integer
  (value: datatype_of_asn1_type INTEGER)
: GTot (the_asn1_tag INTEGER & asn1_value_int32_of_type INTEGER)

///
/// A pair of aux parser/serializer, which explicitly coerce the `INTEGER` value
/// between the subtype used by `INTEGER` value parser/serialzier and `INTEGER`
/// TLV parser/serializer.
///
/// NOTE: I found that have this aux parser explicitly defined will make the prove of
///       `_unfold` lemmas simpler.
///

/// Convert an `INTEGER` value from the subtype used by its value parser to the subtype
/// used by its TLV parser/serializer
/// (value : subtype_{value}) <: subtype_{TLV}
noextract
val synth_asn1_integer_V
  (tag: (the_asn1_tag INTEGER & asn1_value_int32_of_type INTEGER))
  (value: datatype_of_asn1_type INTEGER { v (snd tag) == length_of_asn1_integer value })
: GTot (refine_with_tag parser_tag_of_asn1_integer tag)

/// Convert an `INTEGER` value from the subtype used by its TLV parser to the subtype
/// used by its value parser/serializer
/// (value : subtype_{TLV}) <: subtype_{value}
noextract
val synth_asn1_integer_V_inverse
  (tag: (the_asn1_tag INTEGER & asn1_value_int32_of_type INTEGER))
  (value': refine_with_tag parser_tag_of_asn1_integer tag)
: GTot (value: datatype_of_asn1_type INTEGER {
               v (snd tag) == length_of_asn1_integer value /\
               value' == synth_asn1_integer_V tag value })

///
/// Aux parser
///
noextract
val parse_asn1_integer_V
  (tag: (the_asn1_tag INTEGER & asn1_value_int32_of_type INTEGER))
: parser (weak_kind_of_type INTEGER) (refine_with_tag parser_tag_of_asn1_integer tag)

///
/// Aux serializer
///
noextract
val serialize_asn1_integer_V
  (tag: (the_asn1_tag INTEGER & asn1_value_int32_of_type INTEGER))
: serializer (parse_asn1_integer_V tag)

///
/// Lemmas
///

/// Reveal the computation of parse
val lemma_parse_asn1_integer_V_unfold
  (tag: (the_asn1_tag INTEGER & asn1_value_int32_of_type INTEGER))
  (input: bytes)
: Lemma (
  parse (parse_asn1_integer_V tag) input ==
 (match parse (parse_asn1_integer (v (snd tag))) input with
  | None -> None
  | Some (value, consumed) ->  Some (synth_asn1_integer_V tag value, consumed)))


inline_for_extraction noextract
let parse_asn1_integer_TLV_kind
: parser_kind
= parse_asn1_tag_kind
  `and_then_kind`
  parse_asn1_length_kind_of_type INTEGER
  `and_then_kind`
  weak_kind_of_type INTEGER

//////////////////////////////////////////////////////////
///
/// ASN1 `INTEGER` TLV Parser
///
noextract
val parse_asn1_integer_TLV
: parser parse_asn1_integer_TLV_kind (datatype_of_asn1_type INTEGER)

///
/// ASN1 `INTEGER` TLV Serialzier
///
noextract
val serialize_asn1_integer_TLV
: serializer parse_asn1_integer_TLV

///
/// Lemmas
///

/// Reveal the computation of parse

val lemma_parse_asn1_integer_TLV_unfold
  (input: bytes)
: Lemma (
  parse parse_asn1_integer_TLV input ==
 (match parse (parse_asn1_tag_of_type INTEGER) input with
  | None -> None
  | Some (tag, consumed_tag) ->
    (let input_LV = Seq.slice input consumed_tag (Seq.length input) in
     match parse (parse_asn1_length_of_type INTEGER) input_LV with
     | None -> None
     | Some (len, consumed_len) ->
     (let input_V = Seq.slice input_LV consumed_len (Seq.length input_LV) in
      match parse (parse_asn1_integer (v len)) input_V with
      | None -> None
      | Some (value, consumed_value) ->
             Some ((synth_asn1_integer_V (tag, len) value),
                   (consumed_tag + consumed_len + consumed_value <: consumed_length input)))
  )))

/// Reveal the computation of serialize

val lemma_serialize_asn1_integer_TLV_unfold
  (value: datatype_of_asn1_type INTEGER)
: Lemma (
  serialize serialize_asn1_integer_TLV value ==
  serialize (serialize_asn1_tag_of_type INTEGER) INTEGER
  `Seq.append`
  serialize (serialize_asn1_length_of_type INTEGER) (u (length_of_asn1_integer value))
  `Seq.append`
  serialize (serialize_asn1_integer (length_of_asn1_integer value)) value)

/// Reveal the size of a serialzation

val lemma_serialize_asn1_integer_TLV_size
  (value: datatype_of_asn1_type INTEGER)
: Lemma (
  let length = length_of_asn1_integer value in
  let len: asn1_value_int32_of_type INTEGER = u length in
  Seq.length (serialize serialize_asn1_integer_TLV value) ==
  1 + length_of_asn1_length len + length
)
