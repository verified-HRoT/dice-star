module ASN1.Spec.SEQUENCE

open ASN1.Base
open ASN1.Spec.Tag
open ASN1.Spec.Length
open LowParse.Bytes
open LowParse.Spec.FLData

open FStar.Integers

/// ASN.1 SEQUENCE Tag-Length parser/serializer
///
///
let parse_asn1_sequence_TL_kind
: parser_kind
= parse_asn1_tag_kind
  `and_then_kind`
  parse_asn1_length_kind_of_type SEQUENCE

let parse_asn1_sequence_TL
: parser parse_asn1_sequence_TL_kind (the_asn1_type SEQUENCE & asn1_int32_of_type SEQUENCE)
= parse_the_asn1_tag SEQUENCE
  `nondep_then`
  parse_asn1_length_of_type SEQUENCE

let serialize_asn1_sequence_TL
: serializer parse_asn1_sequence_TL
= serialize_the_asn1_tag SEQUENCE
  `serialize_nondep_then`
  serialize_asn1_length

/// Tagging function
///
///
let parser_tag_of_asn1_sequence
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (data: t { asn1_length_inbound_of_type SEQUENCE (Seq.length (serialize s data)) } )
: GTot (the_asn1_type SEQUENCE & asn1_int32_of_type SEQUENCE)
= (SEQUENCE, u (Seq.length (serialize s data)))

let synth_asn1_sequence_value
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (tag: (the_asn1_type SEQUENCE & asn1_int32_of_type SEQUENCE))
  (y: parse_fldata_strong_t s (v (snd tag)))
: GTot (data: refine_with_tag (parser_tag_of_asn1_sequence s) tag)
= y <: refine_with_tag (parser_tag_of_asn1_sequence s) tag

let synth_asn1_sequence_value_inverse
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (tag: (the_asn1_type SEQUENCE & asn1_int32_of_type SEQUENCE))
  (data: refine_with_tag (parser_tag_of_asn1_sequence s) tag)
: GTot (y: parse_fldata_strong_t s (v (snd tag)){ data == synth_asn1_sequence_value s tag y })
= data <: refine_with_tag (parser_tag_of_asn1_sequence s) tag

/// ASN.1 SEQUENCE value parser/serializer
///
///
let parse_asn1_sequence_value
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (tag: the_asn1_type SEQUENCE & asn1_int32_of_type SEQUENCE)
: parser (parse_fldata_kind (v (snd tag)) k) (refine_with_tag (parser_tag_of_asn1_sequence s) tag)
= serializer_correct_implies_complete p s;
  parse_fldata_strong s (v (snd tag))
  `parse_synth`
  synth_asn1_sequence_value s tag

let parse_asn1_sequence_value_weak
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (tag: the_asn1_type SEQUENCE & asn1_int32_of_type SEQUENCE)
: parser (weak_kind_of_type SEQUENCE) (refine_with_tag (parser_tag_of_asn1_sequence s) tag)
= weak_kind_of_type SEQUENCE
  `weaken`
  parse_asn1_sequence_value s tag

let serialize_asn1_sequence_value
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (tag: the_asn1_type SEQUENCE & asn1_int32_of_type SEQUENCE)
: serializer (parse_asn1_sequence_value s tag)
= serializer_correct_implies_complete p s;
  serialize_synth
  (* p1 *) (parse_fldata_strong s (v (snd tag)))
  (* f2 *) (synth_asn1_sequence_value s tag)
  (* s1 *) (serialize_fldata_strong s (v (snd tag)))
  (* g1 *) (synth_asn1_sequence_value_inverse s tag)
  (* prf*) ()

let serialize_asn1_sequence_value_weak
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (tag: the_asn1_type SEQUENCE & asn1_int32_of_type SEQUENCE)
: serializer (parse_asn1_sequence_value_weak s tag)
= weak_kind_of_type SEQUENCE
  `serialize_weaken`
  serialize_asn1_sequence_value s tag

/// Specialized TLV parser/serializer
///
///

let parse_asn1_sequence_TLV
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
= parse_tagged_union
  (* pt *) (parse_asn1_sequence_TL)
  (* tg *) (parser_tag_of_asn1_sequence s)
  (* p  *) (parse_asn1_sequence_value_weak s)

let serialize_asn1_sequence_TLV
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
: Tot (serializer (parse_asn1_sequence_TLV s))
= serialize_tagged_union
  (* st *) (serialize_asn1_sequence_TL)
  (* tg *) (parser_tag_of_asn1_sequence s)
  (* s  *) (serialize_asn1_sequence_value_weak s)


