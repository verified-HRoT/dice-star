module ASN1.Spec.Value.Envelop

open ASN1.Base
open ASN1.Spec.Base
open ASN1.Spec.Tag
open ASN1.Spec.Length
open LowParse.Bytes
open LowParse.Spec.FLData

open FStar.Integers

(* NOTE: Read after `ASN1.Spec.Tag`, `ASN1.Spec.Length`, `ASN1.Spec.Value.*` *)

(* NOTE: Use `parse_fldata_strong` to construct fixed-length parsers (with the strong prefix proeprty),
         where these fixed-length is runtimely parsed.
 *)

// unfold
inline_for_extraction
let inbound_envelop_tag_with_value_of
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (a: asn1_tag_t)
  (s: serializer p)
= x: t{ asn1_value_length_inbound_of_type a (length_of_opaque_serialization s x) }

/// Tagging function
///
noextract
let parser_tag_of_asn1_envelop_tag_with
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (a: asn1_tag_t)
  (s: serializer p)
  (data: inbound_envelop_tag_with_value_of a s )
: GTot (the_asn1_tag a & asn1_value_int32_of_type a)
= (a, u (Seq.length (serialize s data)))

noextract
let synth_asn1_envelop_tag_with
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (a: asn1_tag_t)
  (s: serializer p)
  (tag: (the_asn1_tag a & asn1_value_int32_of_type a))
  (y: parse_fldata_strong_t s (v (snd tag)))
: GTot (refine_with_tag (parser_tag_of_asn1_envelop_tag_with a s) tag)
= y <: refine_with_tag (parser_tag_of_asn1_envelop_tag_with a s) tag

noextract
let synth_asn1_envelop_tag_with_inverse
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (a: asn1_tag_t)
  (s: serializer p)
  (tag: (the_asn1_tag a & asn1_value_int32_of_type a))
  (data: refine_with_tag (parser_tag_of_asn1_envelop_tag_with a s) tag)
: GTot (y: parse_fldata_strong_t s (v (snd tag)){ data == synth_asn1_envelop_tag_with a s tag y })
= data <: refine_with_tag (parser_tag_of_asn1_envelop_tag_with a s) tag

/// ASN.1 a value parser/serializer
///
noextract
let parse_asn1_envelop_tag_with
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (a: asn1_tag_t)
  (s: serializer p)
  (tag: the_asn1_tag a & asn1_value_int32_of_type a)
: parser (parse_fldata_kind (v (snd tag)) k) (refine_with_tag (parser_tag_of_asn1_envelop_tag_with a s) tag)
= serializer_correct_implies_complete p s;
  parse_fldata_strong s (v (snd tag))
  `parse_synth`
  synth_asn1_envelop_tag_with a s tag

noextract
let lemma_parse_asn1_envelop_tag_with_unfold
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (a: asn1_tag_t)
  (s: serializer p)
  (tag: the_asn1_tag a & asn1_value_int32_of_type a)
  (input: bytes)
: Lemma (
  parse (parse_asn1_envelop_tag_with a s tag) input ==
 (match parse (parse_fldata_strong s (v (snd tag))) input with
  | None -> None
  | Some (value, consumed) -> Some (synth_asn1_envelop_tag_with a s tag value, consumed)))
= parse_synth_eq
  (* p1 *) (parse_fldata_strong s (v (snd tag)))
  (* f2 *) (synth_asn1_envelop_tag_with a s tag)
  (* in *) (input)

noextract
let parse_asn1_envelop_tag_with_weak
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (a: asn1_tag_t)
  (s: serializer p)
  (tag: the_asn1_tag a & asn1_value_int32_of_type a)
: parser (weak_kind_of_type a) (refine_with_tag (parser_tag_of_asn1_envelop_tag_with a s) tag)
= weak_kind_of_type a
  `weaken`
  parse_asn1_envelop_tag_with a s tag

noextract
let serialize_asn1_envelop_tag_with
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (a: asn1_tag_t)
  (s: serializer p)
  (tag: the_asn1_tag a & asn1_value_int32_of_type a)
: serializer (parse_asn1_envelop_tag_with a s tag)
= serializer_correct_implies_complete p s;
  serialize_synth
  (* p1 *) (parse_fldata_strong s (v (snd tag)))
  (* f2 *) (synth_asn1_envelop_tag_with a s tag)
  (* s1 *) (serialize_fldata_strong s (v (snd tag)))
  (* g1 *) (synth_asn1_envelop_tag_with_inverse a s tag)
  (* prf*) ()

// noextract
// let predicate_serialize_asn1_envelop_tag_with_unfold
//   (#k: parser_kind)
//   (#t: Type0)
//   (#p: parser k t)
//   (a: asn1_tag_t)
//   (s: serializer p)
//   (tag: the_asn1_tag a & asn1_value_int32_of_type a)
//   (value: refine_with_tag (parser_tag_of_asn1_envelop_tag_with a s) tag)
// : Type0
// = serialize
//     (serialize_fldata_strong s (v (snd tag)))
//     (synth_asn1_envelop_tag_with_inverse a s tag value)
//   == serialize (serialize_asn1_envelop_tag_with a s tag) value

noextract
let lemma_serialize_asn1_envelop_tag_with_unfold
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (a: asn1_tag_t)
  (s: serializer p)
  (tag: the_asn1_tag a & asn1_value_int32_of_type a)
  (value: refine_with_tag (parser_tag_of_asn1_envelop_tag_with a s) tag)
: Lemma (
  serialize
    (serialize_fldata_strong s (v (snd tag)))
    (synth_asn1_envelop_tag_with_inverse a s tag value)
  == serialize (serialize_asn1_envelop_tag_with a s tag) value
)
= serializer_correct_implies_complete p s;
  serialize_synth_eq
  (* p1 *) (parse_fldata_strong s (v (snd tag)))
  (* f2 *) (synth_asn1_envelop_tag_with a s tag)
  (* s1 *) (serialize_fldata_strong s (v (snd tag)))
  (* g1 *) (synth_asn1_envelop_tag_with_inverse a s tag)
  (* prf*) ()
  (* val*) (value)

noextract
let serialize_asn1_envelop_tag_with_weak
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (a: asn1_tag_t)
  (s: serializer p)
  (tag: the_asn1_tag a & asn1_value_int32_of_type a)
: serializer (parse_asn1_envelop_tag_with_weak a s tag)
= weak_kind_of_type a
  `serialize_weaken`
  serialize_asn1_envelop_tag_with a s tag

/// Specialized TLV parser/serializer
///
///

let parse_asn1_envelop_tag_with_TLV_kind
  (a: asn1_tag_t)
: parser_kind
= parse_asn1_tag_kind
  `and_then_kind`
  parse_asn1_length_kind_of_type a
  `and_then_kind`
  weak_kind_of_type a

noextract
let parse_asn1_envelop_tag_with_TLV
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (a: asn1_tag_t)
  (s: serializer p)
: parser (parse_asn1_envelop_tag_with_TLV_kind a) (inbound_envelop_tag_with_value_of a s)
= parse_tagged_union
  (* pt *) (parse_asn1_tag_of_type a
            `nondep_then`
            parse_asn1_length_of_type a)
  (* tg *) (parser_tag_of_asn1_envelop_tag_with a s)
  (* p  *) (parse_asn1_envelop_tag_with_weak a s)

noextract
let serialize_asn1_envelop_tag_with_TLV
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (a: asn1_tag_t)
  (s: serializer p)
: Tot (serializer (parse_asn1_envelop_tag_with_TLV a s))
= serialize_tagged_union
  (* st *) (serialize_asn1_tag_of_type a
            `serialize_nondep_then`
            serialize_asn1_length_of_type a)
  (* tg *) (parser_tag_of_asn1_envelop_tag_with a s)
  (* s  *) (serialize_asn1_envelop_tag_with_weak a s)

#push-options "--z3rlimit 32"
let predicate_serialize_asn1_envelop_tag_with_TLV_unfold
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (a: asn1_tag_t)
  (s: serializer p)
  (value: inbound_envelop_tag_with_value_of a s)
: Type0
= serialize (serialize_asn1_envelop_tag_with_TLV a s) value ==
  serialize (serialize_asn1_tag_of_type a) a
  `Seq.append`
  serialize (serialize_asn1_length_of_type a) (u (length_of_opaque_serialization (serialize_asn1_envelop_tag_with a s (parser_tag_of_asn1_envelop_tag_with a s value)) value))
  `Seq.append`
  serialize (serialize_asn1_envelop_tag_with a s (parser_tag_of_asn1_envelop_tag_with a s value)) value

let lemma_serialize_asn1_envelop_tag_with_TLV_unfold
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (a: asn1_tag_t)
  (s: serializer p)
  (value: inbound_envelop_tag_with_value_of a s)
: Lemma ( predicate_serialize_asn1_envelop_tag_with_TLV_unfold a s value )
= //lemma_serialize_asn1_envelop_tag_with_unfold s (parser_tag_of_asn1_envelop_tag_with s value) value;
  serialize_nondep_then_eq
  (* s1 *) (serialize_asn1_tag_of_type a)
  (* s2 *) (serialize_asn1_length_of_type a)
  (* val*) (parser_tag_of_asn1_envelop_tag_with a s value);
  serialize_tagged_union_eq
  (* st *) (serialize_asn1_tag_of_type a
            `serialize_nondep_then`
            serialize_asn1_length_of_type a)
  (* tg *) (parser_tag_of_asn1_envelop_tag_with a s)
  (* s  *) (serialize_asn1_envelop_tag_with_weak a s)
  (* val*) (value)


let predicate_serialize_asn1_envelop_tag_with_TLV_size
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (a: asn1_tag_t)
  (s: serializer p)
  (value: inbound_envelop_tag_with_value_of a s)
: Type0
= let length: asn1_value_length_of_type a = Seq.length (serialize s value) in
  let len: asn1_value_int32_of_type a = u length in
  (* exact size *)
  Seq.length (serialize (serialize_asn1_envelop_tag_with_TLV a s) value)
  == 1 + length_of_asn1_length len + length /\
  (* upper bound *)
  Seq.length (serialize (serialize_asn1_envelop_tag_with_TLV a s) value)
  <= length + 6 /\
  Seq.length (serialize (serialize_asn1_envelop_tag_with_TLV a s) value)
  <= asn1_TLV_length_max_of_type a /\
  Seq.length (serialize s value)
  <= asn1_value_length_max_of_type a

let lemma_serialize_asn1_envelop_tag_with_TLV_size
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (a: asn1_tag_t)
  (s: serializer p)
  (value: inbound_envelop_tag_with_value_of a s)
: Lemma ( predicate_serialize_asn1_envelop_tag_with_TLV_size a s value )
= let length: asn1_value_length_of_type a = Seq.length (serialize s value) in
  let len: asn1_value_int32_of_type a = u length in
  lemma_serialize_asn1_envelop_tag_with_TLV_unfold a s value;
  lemma_serialize_asn1_tag_of_type_size a a;
  lemma_serialize_asn1_length_size len;
  serialize_asn1_length_of_type_eq a len

noextract unfold
let length_of_asn1_envelop_tag_with_TLV
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (a: asn1_tag_t)
  (s: serializer p)
  (value: inbound_envelop_tag_with_value_of a s)
: GTot (l: asn1_TLV_length_of_type a { l == Seq.length (serialize (serialize_asn1_envelop_tag_with_TLV a s) value) })
= let length = Seq.length (serialize s value) in
  let len: asn1_int32 = u length in
  lemma_serialize_asn1_envelop_tag_with_TLV_unfold a s value;
  lemma_serialize_asn1_envelop_tag_with_TLV_size a s value;
  1 + length_of_asn1_length len + length
#pop-options

inline_for_extraction
let coerce_envelop
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (a1: asn1_tag_t { match a1 with | SEQUENCE | SET | OCTET_STRING | CUSTOM_TAG _ _ _ -> True | _ -> False })
  (a2: asn1_tag_t { match a2 with | SEQUENCE | SET | OCTET_STRING | CUSTOM_TAG _ _ _ -> True | _ -> False })
  (s: serializer p)
  (x1: inbound_envelop_tag_with_value_of a1 (serialize_asn1_envelop_tag_with_TLV a2 s))
: inbound_envelop_tag_with_value_of a2 s
= x1

inline_for_extraction
let coerce_envelop_back
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (a1: asn1_tag_t { match a1 with | SEQUENCE | SET | OCTET_STRING | CUSTOM_TAG _ _ _ -> True | _ -> False })
  (a2: asn1_tag_t { match a2 with | SEQUENCE | SET | OCTET_STRING | CUSTOM_TAG _ _ _ -> True | _ -> False })
  (s: serializer p)
  (x1: inbound_envelop_tag_with_value_of a2 s
       { asn1_value_length_inbound_of_type a1 (length_of_opaque_serialization (serialize_asn1_envelop_tag_with_TLV a2 s) x1) })
: inbound_envelop_tag_with_value_of a1 (serialize_asn1_envelop_tag_with_TLV a2 s)
= x1

