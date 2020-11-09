module ASN1.Spec.Value.BOOLEAN

open ASN1.Spec.Base
open LowParse.Spec.Int

open ASN1.Base

(* NOTE: Read after `ASN1.Spec.Tag`, `ASN1.Spec.Length` *)

(* NOTE: This module defines:
         1) The ASN1 `BOOLEAN` Value Parser and Serializer
         2) The ASN1 `BOOLEAN` TLV Parser and Serializer

         And each part is organized as:
         1) Aux (ghost) functions with prefix `filter_` to filter out invalid input bytes
         2) Aux (ghost) functions with prefix `synth_` to decode the valid input bytes into our
            representation of BOOLEAN values. These functions are injective.
         3) Aux (ghost) functions with prefix `synth_` and suffix `_inverse` to encode our
            representation of BOOLEAN into bytes. These functions are the inverse of
            corresponding synth functions.
         4) Functions with the prefix `parse_` are parsers constructed using parser combinators and
            aux functions.
         5) Functions with the prefix `serialize_` are serializers constructed using serializer
            combinators and aux functions.
         6) Lemma with suffix `_unfold` reveals the computation of parser/serialzier.
         7) Lemma with suffix `_size` reveals the length of a serialization.
*)

(* BOOLEAN primitive *)
/// filter valid input bytes
noextract
val filter_asn1_boolean
  (b: byte)
: GTot bool

/// decode input bytes
noextract
val synth_asn1_boolean
  (b: parse_filter_refine filter_asn1_boolean)
: GTot (datatype_of_asn1_type BOOLEAN)

/// encode input bytes
noextract
val synth_asn1_boolean_inverse
  (b: datatype_of_asn1_type BOOLEAN)
: GTot (r: parse_filter_refine filter_asn1_boolean{synth_asn1_boolean r == b})

inline_for_extraction noextract
let parse_asn1_boolean_kind = strong_parser_kind 1 1 None

noextract
val parse_asn1_boolean
: parser parse_asn1_boolean_kind (datatype_of_asn1_type BOOLEAN)

val lemma_parse_asn1_boolean_unfold
  (input: bytes)
: Lemma (
  parse parse_asn1_boolean input ==
 (match parse parse_u8 input with
  | Some (x, consumed) -> if filter_asn1_boolean x then
                          ( Some (synth_asn1_boolean x, consumed) )
                          else
                          ( None )
  | None -> None) /\
 (Some? (parse parse_asn1_boolean input) ==>
   Seq.length input > 0 /\
   parse parse_u8 input == Some (input.[0], 1)))

noextract
val serialize_asn1_boolean
: serializer parse_asn1_boolean

val lemma_serialize_asn1_boolean_unfold
  (b: datatype_of_asn1_type BOOLEAN)
: Lemma (
  serialize serialize_u8 (synth_asn1_boolean_inverse b)
  `Seq.equal`
  Seq.create 1 (synth_asn1_boolean_inverse b) /\
  serialize serialize_asn1_boolean b
  `Seq.equal`
  serialize serialize_u8 (synth_asn1_boolean_inverse b))

val lemma_serialize_asn1_boolean_size
  (b: datatype_of_asn1_type BOOLEAN)
: Lemma (
  Seq.length (serialize serialize_asn1_boolean b) == 1)


/// Specialized TLV
///

open ASN1.Spec.Tag
open ASN1.Spec.Length

val synth_asn1_boolean_TLV
  (a: (the_asn1_tag BOOLEAN * asn1_value_int32_of_type BOOLEAN) * datatype_of_asn1_type BOOLEAN)
: GTot (datatype_of_asn1_type BOOLEAN)

val synth_asn1_boolean_TLV_inverse
  (x: datatype_of_asn1_type BOOLEAN)
: GTot (a: ((the_asn1_tag BOOLEAN * asn1_value_int32_of_type BOOLEAN) * datatype_of_asn1_type BOOLEAN){x == synth_asn1_boolean_TLV a})

inline_for_extraction noextract
let parse_asn1_boolean_TLV_kind
: parser_kind
= strong_parser_kind 3 3 None

noextract
val parse_asn1_boolean_TLV
: parser parse_asn1_boolean_TLV_kind (datatype_of_asn1_type BOOLEAN)

// #push-options "--z3rlimit 16 --initial_ifuel 4"
// val lemma_parse_asn1_boolean_TLV_unfold
//   (input_TLV: bytes)
// : Lemma (
//   parse parse_asn1_boolean_TLV input_TLV ==
//  (parser_kind_prop_equiv parse_asn1_tag_kind (parse_asn1_tag_of_type BOOLEAN);
//   match parse (parse_asn1_tag_of_type BOOLEAN) input_TLV with
//   | None -> None
//   | Some (BOOLEAN, 1) ->
//     (parser_kind_prop_equiv (parse_asn1_length_kind_of_type BOOLEAN) (parse_asn1_length_of_type BOOLEAN);
//      let input_LV = Seq.slice input_TLV 1 (Seq.length input_TLV) in
//      match parse (parse_asn1_length_of_type BOOLEAN) input_LV with
//      | None -> None
//      | Some (1ul, 1) ->
//        (parser_kind_prop_equiv parse_asn1_boolean_kind parse_asn1_boolean;
//         let input_V = Seq.slice input_LV 1 (Seq.length input_LV) in
//         match parse parse_asn1_boolean input_V with
//         | None -> None
//         | Some (value, 1) -> Some (value, (1 + 1 + 1 <: consumed_length input_TLV)))))
// )

noextract
val serialize_asn1_boolean_TLV
: serializer parse_asn1_boolean_TLV

(* NOTE: How far should we unfold the computation? *)
val lemma_serialize_asn1_boolean_TLV_unfold
  (value: datatype_of_asn1_type BOOLEAN)
: Lemma (
  serialize serialize_asn1_boolean_TLV value
  `Seq.equal`
 (serialize (serialize_asn1_tag_of_type BOOLEAN) BOOLEAN
  `Seq.append`
  serialize (serialize_asn1_length_of_type BOOLEAN) 1ul
  `Seq.append`
  serialize serialize_asn1_boolean value)
)

(* NOTE: Should we just combine this lemma into `_unfold` lemmas? *)
val lemma_serialize_asn1_boolean_TLV_size
  (value: datatype_of_asn1_type BOOLEAN)
: Lemma (
  Seq.length (serialize serialize_asn1_boolean_TLV value) == 3)

(* Refined Versions *)

(* BOOLEAN true *)
let filter_asn1_boolean_true
  (x: datatype_of_asn1_type BOOLEAN)
: GTot (bool)
= x = true

let asn1_boolean_true_t
: Type
= parse_filter_refine filter_asn1_boolean_true

let asn1_boolean_true: asn1_boolean_true_t = true

let parse_asn1_boolean_TLV_true
: parser parse_asn1_boolean_TLV_kind asn1_boolean_true_t
= parse_asn1_boolean_TLV
  `parse_filter`
  filter_asn1_boolean_true

let serialize_asn1_boolean_TLV_true
: serializer parse_asn1_boolean_TLV_true
= serialize_asn1_boolean_TLV
  `serialize_filter`
  filter_asn1_boolean_true

(* BOOLEAN false *)
let filter_asn1_boolean_false
  (x: datatype_of_asn1_type BOOLEAN)
: GTot (bool)
= x = false

let asn1_boolean_false_t
: Type
= parse_filter_refine filter_asn1_boolean_false

let asn1_boolean_false: asn1_boolean_false_t = false

let parse_asn1_boolean_TLV_false
: parser parse_asn1_boolean_TLV_kind asn1_boolean_false_t
= parse_asn1_boolean_TLV
  `parse_filter`
  filter_asn1_boolean_false

let serialize_asn1_boolean_TLV_false
: serializer parse_asn1_boolean_TLV_false
= serialize_asn1_boolean_TLV
  `serialize_filter`
  filter_asn1_boolean_false
