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
noextract
let parse_asn1_sequence_TL_kind
: parser_kind
= parse_asn1_tag_kind
  `and_then_kind`
  parse_asn1_length_kind_of_type SEQUENCE

noextract
let parse_asn1_sequence_TL
: parser parse_asn1_sequence_TL_kind (the_asn1_type SEQUENCE & asn1_value_int32_of_type SEQUENCE)
= parse_asn1_tag_of_type SEQUENCE
  `nondep_then`
  parse_asn1_length_of_type SEQUENCE

noextract
let parse_asn1_sequence_TL_unfold
  (input: bytes)
: Lemma (
  parse parse_asn1_sequence_TL input ==
 (match parse (parse_asn1_tag_of_type SEQUENCE) input with
  | None -> None
  | Some (SEQUENCE, consumed_tag) ->
      (let input_len = Seq.slice input consumed_tag (Seq.length input) in
       match parse (parse_asn1_length_of_type SEQUENCE) input_len with
       | None -> None
       | Some (len, consumed_len) -> Some ((SEQUENCE, len), (consumed_tag + consumed_len <: consumed_length input)))))
= nondep_then_eq
  (* p1 *) (parse_asn1_tag_of_type SEQUENCE)
  (* p2 *) (parse_asn1_length_of_type SEQUENCE)
  (* in *) (input)

noextract
let serialize_asn1_sequence_TL
: serializer parse_asn1_sequence_TL
= serialize_asn1_tag_of_type SEQUENCE
  `serialize_nondep_then`
  serialize_asn1_length_of_type SEQUENCE

noextract
let serialize_asn1_sequence_TL_unfold
  (tl: (the_asn1_type SEQUENCE & asn1_value_int32_of_type SEQUENCE))
: Lemma (
  serialize serialize_asn1_sequence_TL tl ==
  serialize (serialize_asn1_tag_of_type SEQUENCE) (fst tl)
  `Seq.append`
  serialize (serialize_asn1_length_of_type SEQUENCE) (snd tl))
= serialize_nondep_then_eq
  (* s1 *) (serialize_asn1_tag_of_type SEQUENCE)
  (* s2 *) (serialize_asn1_length_of_type SEQUENCE)
  (* val*) (tl)

/// Tagging function
///
noextract
let parser_tag_of_asn1_sequence
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (data: t { asn1_value_length_inbound_of_type SEQUENCE (Seq.length (serialize s data)) } )
: GTot (the_asn1_type SEQUENCE & asn1_value_int32_of_type SEQUENCE)
= (SEQUENCE, u (Seq.length (serialize s data)))

noextract
let synth_asn1_sequence_value
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (tag: (the_asn1_type SEQUENCE & asn1_value_int32_of_type SEQUENCE))
  (y: parse_fldata_strong_t s (v (snd tag)))
: GTot (data: refine_with_tag (parser_tag_of_asn1_sequence s) tag)
= y <: refine_with_tag (parser_tag_of_asn1_sequence s) tag

noextract
let synth_asn1_sequence_value_inverse
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (tag: (the_asn1_type SEQUENCE & asn1_value_int32_of_type SEQUENCE))
  (data: refine_with_tag (parser_tag_of_asn1_sequence s) tag)
: GTot (y: parse_fldata_strong_t s (v (snd tag)){ data == synth_asn1_sequence_value s tag y })
= data <: refine_with_tag (parser_tag_of_asn1_sequence s) tag

/// ASN.1 SEQUENCE value parser/serializer
///
noextract
let parse_asn1_sequence_value
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (tag: the_asn1_type SEQUENCE & asn1_value_int32_of_type SEQUENCE)
: parser (parse_fldata_kind (v (snd tag)) k) (refine_with_tag (parser_tag_of_asn1_sequence s) tag)
= serializer_correct_implies_complete p s;
  parse_fldata_strong s (v (snd tag))
  `parse_synth`
  synth_asn1_sequence_value s tag

noextract
let parse_asn1_sequence_value_unfold
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (tag: the_asn1_type SEQUENCE & asn1_value_int32_of_type SEQUENCE)
  (input: bytes)
: Lemma (
  parse (parse_asn1_sequence_value s tag) input ==
 (match parse (parse_fldata_strong s (v (snd tag))) input with
  | None -> None
  | Some (value, consumed) -> Some (synth_asn1_sequence_value s tag value, consumed)))
= parse_synth_eq
  (* p1 *) (parse_fldata_strong s (v (snd tag)))
  (* f2 *) (synth_asn1_sequence_value s tag)
  (* in *) (input)

noextract
let parse_asn1_sequence_value_weak
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (tag: the_asn1_type SEQUENCE & asn1_value_int32_of_type SEQUENCE)
: parser (weak_kind_of_type SEQUENCE) (refine_with_tag (parser_tag_of_asn1_sequence s) tag)
= weak_kind_of_type SEQUENCE
  `weaken`
  parse_asn1_sequence_value s tag

noextract
let serialize_asn1_sequence_value
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (tag: the_asn1_type SEQUENCE & asn1_value_int32_of_type SEQUENCE)
: serializer (parse_asn1_sequence_value s tag)
= serializer_correct_implies_complete p s;
  serialize_synth
  (* p1 *) (parse_fldata_strong s (v (snd tag)))
  (* f2 *) (synth_asn1_sequence_value s tag)
  (* s1 *) (serialize_fldata_strong s (v (snd tag)))
  (* g1 *) (synth_asn1_sequence_value_inverse s tag)
  (* prf*) ()

noextract
let serialize_asn1_sequence_value_unfold
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (tag: the_asn1_type SEQUENCE & asn1_value_int32_of_type SEQUENCE)
  (value: refine_with_tag (parser_tag_of_asn1_sequence s) tag)
: Lemma (
  serialize
    (serialize_fldata_strong s (v (snd tag)))
    (synth_asn1_sequence_value_inverse s tag value)
  == serialize (serialize_asn1_sequence_value s tag) value
)
= serializer_correct_implies_complete p s;
  serialize_synth_eq
  (* p1 *) (parse_fldata_strong s (v (snd tag)))
  (* f2 *) (synth_asn1_sequence_value s tag)
  (* s1 *) (serialize_fldata_strong s (v (snd tag)))
  (* g1 *) (synth_asn1_sequence_value_inverse s tag)
  (* prf*) ()
  (* val*) (value)

noextract
let serialize_asn1_sequence_value_weak
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (tag: the_asn1_type SEQUENCE & asn1_value_int32_of_type SEQUENCE)
: serializer (parse_asn1_sequence_value_weak s tag)
= weak_kind_of_type SEQUENCE
  `serialize_weaken`
  serialize_asn1_sequence_value s tag

/// Specialized TLV parser/serializer
///
///

noextract
let parse_asn1_sequence_TLV
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
: parser _ (x: t{ asn1_value_length_inbound_of_type SEQUENCE (Seq.length (serialize s x)) })
= parse_tagged_union
  (* pt *) (parse_asn1_sequence_TL)
  (* tg *) (parser_tag_of_asn1_sequence s)
  (* p  *) (parse_asn1_sequence_value_weak s)

#push-options "--query_stats --z3rlimit 16"
noextract
let parse_asn1_sequence_TLV_unfold
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (input: bytes)
: Lemma (
  parse (parse_asn1_sequence_TLV s) input ==
 (match parse parse_asn1_sequence_TL input with
  | None -> None
  | Some (tag, consumed_tag) ->
      (let input_value = Seq.slice input consumed_tag (Seq.length input) in
       match parse (parse_asn1_sequence_value s tag) input_value with
       | None -> None
       | Some (value, consumed_value) ->
           Some ( (value <: x: t{ asn1_value_length_inbound_of_type SEQUENCE (Seq.length (serialize s x)) })
                , (consumed_tag + consumed_value <: consumed_length input) ))))
= parse_tagged_union_eq
  (* pt *) (parse_asn1_sequence_TL)
  (* tg *) (parser_tag_of_asn1_sequence s)
  (* p  *) (parse_asn1_sequence_value_weak s)
  (* in *) (input)
#pop-options

noextract
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

#push-options "--query_stats --z3rlimit 16"
noextract
let serialize_asn1_sequence_TLV_unfold
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (value: t{ asn1_value_length_inbound_of_type SEQUENCE (Seq.length (serialize s value)) })
: Lemma (
  serialize (serialize_asn1_sequence_TLV s) value ==
  serialize serialize_asn1_sequence_TL (parser_tag_of_asn1_sequence s value)
  `Seq.append`
  serialize (serialize_asn1_sequence_value s (parser_tag_of_asn1_sequence s value)) value
  /\
  serialize (serialize_asn1_sequence_TLV s) value ==
  serialize (serialize_asn1_tag_of_type SEQUENCE) SEQUENCE
  `Seq.append`
  serialize (serialize_asn1_length_of_type SEQUENCE) (u (Seq.length (serialize (serialize_asn1_sequence_value s (parser_tag_of_asn1_sequence s value)) value)))
  `Seq.append`
  serialize (serialize_asn1_sequence_value s (parser_tag_of_asn1_sequence s value)) value
)
= serialize_asn1_sequence_TL_unfold (parser_tag_of_asn1_sequence s value);
  serialize_tagged_union_eq
  (* st *) (serialize_asn1_sequence_TL)
  (* tg *) (parser_tag_of_asn1_sequence s)
  (* s  *) (serialize_asn1_sequence_value_weak s)
  (* val*) (value)

noextract
let serialize_asn1_sequence_TLV_size
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (value: t{ asn1_value_length_inbound_of_type SEQUENCE (Seq.length (serialize s value)) })
: Lemma (
  let length: asn1_value_length_of_type SEQUENCE = Seq.length (serialize s value) in
  let len: asn1_value_int32_of_type SEQUENCE = u length in
  Seq.length (serialize (serialize_asn1_sequence_TLV s) value) ==
  1 + length_of_asn1_length len + length)
= let length: asn1_value_length_of_type SEQUENCE = Seq.length (serialize s value) in
  let len: asn1_value_int32_of_type SEQUENCE = u length in
  serialize_asn1_sequence_TLV_unfold s value;
  serialize_asn1_tag_of_type_size SEQUENCE SEQUENCE;
  serialize_asn1_length_size len;
  serialize_asn1_length_of_type_eq SEQUENCE len

noextract
let length_of_sequence_TLV
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (value: t{ asn1_value_length_inbound_of_type SEQUENCE (Seq.length (serialize s value)) })
: GTot (l: asn1_TLV_length_of_type SEQUENCE { l == Seq.length (serialize (serialize_asn1_sequence_TLV s) value) })
= let length = Seq.length (serialize s value) in
  let len: asn1_int32 = u length in
  serialize_asn1_sequence_TLV_unfold s value;
  serialize_asn1_sequence_TLV_size s value;
  1 + length_of_asn1_length len + length
#pop-options
