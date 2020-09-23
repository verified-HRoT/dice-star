module ASN1.Spec.Value.NULL

open ASN1.Spec.Base

open ASN1.Base
open ASN1.Spec.Tag
open ASN1.Spec.Length

(* NOTE: Read after `ASN1.Spec.Tag`, `ASN1.Spec.Length` *)
(* NOTE: This module defines:
         1) The ASN1 `ASN1_NULL` Value Parser and Serializer
         2) The ASN1 `ASN1_NULL` TLV Parser and Serializer
*)

///////////////////////////////////////////////////////////////
////  ASN1 `ASN1_NULL` Value Parser/Serializer
///////////////////////////////////////////////////////////////

noextract
let parse_asn1_ASN1_NULL_kind = parse_ret_kind

///
/// ASN1 `ASN1_NULL` value parser parses nothing and returns `()`
/// using the `parse_ret` combinator
///
noextract
val parse_asn1_ASN1_NULL
: parser parse_asn1_ASN1_NULL_kind (datatype_of_asn1_type ASN1_NULL)

///
/// ASN1 `ASN1_NULL` value parser serialize `()` to empty bytes
/// using the `serialize_ret` combinator
///
noextract
val serialize_asn1_ASN1_NULL
: serializer parse_asn1_ASN1_NULL

///
/// Lemmas
///

/// Reveal the computation of serialize
val lemma_serialize_asn1_ASN1_NULL_unfold
  (value: datatype_of_asn1_type ASN1_NULL)
: Lemma (
  serialize serialize_asn1_ASN1_NULL value == Seq.empty)

/// Reveal the size of a serialiaztion
val lemma_serialize_asn1_ASN1_NULL_size
  (value: datatype_of_asn1_type ASN1_NULL)
: Lemma (
  Seq.length (serialize serialize_asn1_ASN1_NULL value) == 0)

///////////////////////////////////////////////////////////////
////  ASN1 `ASN1_NULL` TLV Parser/Serializer
///////////////////////////////////////////////////////////////

/// Synthesize the TLV of a `ASN1_NULL` value
noextract
val synth_asn1_ASN1_NULL_TLV
  (a: (the_asn1_tag ASN1_NULL * asn1_value_int32_of_type ASN1_NULL) * datatype_of_asn1_type ASN1_NULL)
: GTot (datatype_of_asn1_type ASN1_NULL)

/// Synthesize th `ASN1_NULL` value from a `ASN1_NULL` TLV
noextract
val synth_asn1_ASN1_NULL_TLV_inverse
  (x: datatype_of_asn1_type ASN1_NULL)
: GTot (a: ((the_asn1_tag ASN1_NULL * asn1_value_int32_of_type ASN1_NULL) * datatype_of_asn1_type ASN1_NULL){x == synth_asn1_ASN1_NULL_TLV a})

inline_for_extraction noextract
let parse_asn1_ASN1_NULL_TLV_kind
: parser_kind
= strong_parser_kind 2 2 None

///
/// `ASN1_NULL` TLV parser
///
noextract
val parse_asn1_ASN1_NULL_TLV
: parser parse_asn1_ASN1_NULL_TLV_kind (datatype_of_asn1_type ASN1_NULL)

///
/// `ASN1_NULL` TLV serialzier
///
noextract
val serialize_asn1_ASN1_NULL_TLV
: serializer parse_asn1_ASN1_NULL_TLV

///
/// Lemmas
///

/// Reveal the computation of parse
val lemma_parse_asn1_ASN1_NULL_TLV_unfold
  (input_TLV: bytes)
: Lemma (
  parse parse_asn1_ASN1_NULL_TLV input_TLV ==
 (match parse (parse_asn1_tag_of_type ASN1_NULL) input_TLV with
  | None -> None
  | Some (ASN1_NULL, consumed_T) ->
    (let input_LV = Seq.slice input_TLV consumed_T (Seq.length input_TLV) in
     match parse (parse_asn1_length_of_type ASN1_NULL) input_LV with
     | None -> None
     | Some (0ul, consumed_L) ->
       (let input_V = Seq.slice input_LV consumed_L (Seq.length input_LV) in
        match parse parse_asn1_ASN1_NULL input_V with
        | None -> None
        | Some (value, consumed_V) -> Some (value, (consumed_T + consumed_L + consumed_V <: consumed_length input_TLV)))))
)

/// Reveal the computation of serialize
val lemma_serialize_asn1_ASN1_NULL_TLV_unfold
  (value: datatype_of_asn1_type ASN1_NULL)
: Lemma (
  serialize serialize_asn1_ASN1_NULL_TLV value
  `Seq.equal`
 (serialize (serialize_asn1_tag_of_type ASN1_NULL) ASN1_NULL
  `Seq.append`
  serialize (serialize_asn1_length_of_type ASN1_NULL) 0ul
  `Seq.append`
  serialize serialize_asn1_ASN1_NULL value)
)

/// Reveal the length of a serialization
val lemma_serialize_asn1_ASN1_NULL_TLV_size
  (value: datatype_of_asn1_type ASN1_NULL)
: Lemma (
  Seq.length (serialize serialize_asn1_ASN1_NULL_TLV value) == 2)
