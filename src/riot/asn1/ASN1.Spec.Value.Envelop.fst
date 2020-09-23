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


/// Tagging function
///
let parser_tag_of_asn1_envelop_tag_with #k #t #p a s data
= (a, u (Seq.length (serialize s data)))

let synth_asn1_envelop_tag_with #k #t #p a s tag y
= y <: refine_with_tag (parser_tag_of_asn1_envelop_tag_with a s) tag

noextract
let synth_asn1_envelop_tag_with_inverse #k #t #p a s tag data
= data <: refine_with_tag (parser_tag_of_asn1_envelop_tag_with a s) tag

/// ASN.1 a value parser/serializer
///
noextract
let parse_asn1_envelop_tag_with #k #t #p a s tag
= serializer_correct_implies_complete p s;
  parse_fldata_strong s (v (snd tag))
  `parse_synth`
  synth_asn1_envelop_tag_with a s tag

let lemma_parse_asn1_envelop_tag_with_unfold #k #t #p a s tag input
= parse_synth_eq
  (* p1 *) (parse_fldata_strong s (v (snd tag)))
  (* f2 *) (synth_asn1_envelop_tag_with a s tag)
  (* in *) (input)

let parse_asn1_envelop_tag_with_weak #k #t #p a s tag
= weak_kind_of_type a
  `weaken`
  parse_asn1_envelop_tag_with a s tag

let serialize_asn1_envelop_tag_with #k #t #p a s tag
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

let lemma_serialize_asn1_envelop_tag_with_unfold #k #t #p a s tag value
= serializer_correct_implies_complete p s;
  serialize_synth_eq
  (* p1 *) (parse_fldata_strong s (v (snd tag)))
  (* f2 *) (synth_asn1_envelop_tag_with a s tag)
  (* s1 *) (serialize_fldata_strong s (v (snd tag)))
  (* g1 *) (synth_asn1_envelop_tag_with_inverse a s tag)
  (* prf*) ()
  (* val*) (value)

let serialize_asn1_envelop_tag_with_weak #k #t #p a s tag
= weak_kind_of_type a
  `serialize_weaken`
  serialize_asn1_envelop_tag_with a s tag

/// Specialized TLV parser/serializer
///
///

let parse_asn1_envelop_tag_with_TLV #k #t #p a s
= parse_tagged_union
  (* pt *) (parse_asn1_tag_of_type a
            `nondep_then`
            parse_asn1_length_of_type a)
  (* tg *) (parser_tag_of_asn1_envelop_tag_with a s)
  (* p  *) (parse_asn1_envelop_tag_with_weak a s)

let serialize_asn1_envelop_tag_with_TLV #k #t #p a s
= serialize_tagged_union
  (* st *) (serialize_asn1_tag_of_type a
            `serialize_nondep_then`
            serialize_asn1_length_of_type a)
  (* tg *) (parser_tag_of_asn1_envelop_tag_with a s)
  (* s  *) (serialize_asn1_envelop_tag_with_weak a s)

#push-options "--z3rlimit 32"
let lemma_serialize_asn1_envelop_tag_with_TLV_unfold #k #t #p a s value
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

let lemma_serialize_asn1_envelop_tag_with_TLV_size #k #t #p a s value
= let length: asn1_value_length_of_type a = Seq.length (serialize s value) in
  let len: asn1_value_int32_of_type a = u length in
  lemma_serialize_asn1_envelop_tag_with_TLV_unfold a s value;
  lemma_serialize_asn1_tag_of_type_size a a;
  lemma_serialize_asn1_length_size len;
  serialize_asn1_length_of_type_eq a len

let length_of_asn1_envelop_tag_with_TLV #k #t #p a s value
= let length = Seq.length (serialize s value) in
  let len: asn1_int32 = u length in
  lemma_serialize_asn1_envelop_tag_with_TLV_unfold a s value;
  lemma_serialize_asn1_envelop_tag_with_TLV_size a s value;
  1 + length_of_asn1_length len + length
#pop-options

let coerce_envelop #k #t #p a1 a2 s x1
= x1

let coerce_envelop_back #k #t #p a1 a2 s x1
= x1

