module X509.BasicFields.Extensions

open ASN1.Spec
open ASN1.Low

open X509.Base
open FStar.Integers

let parse_x509_extensions_TLV #k #t #p s
= x509_extensions_t_inbound s
  `coerce_parser`
  parse_asn1_envelop_tag_with_TLV
  (* tag *) x509_extensions_outmost_explicit_tag
  (*  s  *) s

let serialize_x509_extensions_TLV #k #t #p s
= coerce_parser_serializer
  (* p *) (parse_x509_extensions_TLV s)
  (* s *) (serialize_asn1_envelop_tag_with_TLV
           (* tag *) x509_extensions_outmost_explicit_tag
           (*  s  *) s)
  (*prf*) ()

let lemma_serialize_x509_extensions_TLV_unfold #k #t #p s x
= lemma_serialize_asn1_envelop_tag_with_TLV_unfold x509_extensions_outmost_explicit_tag s x

let lemma_serialize_x509_extensions_TLV_size #k #t #p s x
= lemma_serialize_asn1_envelop_tag_with_TLV_size x509_extensions_outmost_explicit_tag s x

let serialize32_x509_extensions_TLV_backwards #_ #_ #_ #s s32
= coerce_serializer32_backwards
  (* s2  *) (serialize_x509_extensions_TLV s)
  (* s32 *) (serialize32_asn1_envelop_tag_with_TLV_backwards
             (* tag *) x509_extensions_outmost_explicit_tag
             (* s32 *) s32)
  (* prf *) ()


(*)
(* inner sequence *)

let x509_extensions_inner_sequence_t_inbound
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
= inbound_sequence_value_of s

let parse_x509_extensions_inner_sequence_TLV
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
: parser (parse_asn1_envelop_tag_with_TLV_kind SEQUENCE) (x509_extensions_inner_sequence_t_inbound s)
= x509_extensions_inner_sequence_t_inbound s
  `coerce_parser`
  parse_asn1_sequence_TLV s

let serialize_x509_extensions_inner_sequence_TLV
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
: serializer (parse_x509_extensions_inner_sequence_TLV s)
= coerce_parser_serializer
  (* t *) (parse_x509_extensions_inner_sequence_TLV s)
  (* s *) (serialize_asn1_sequence_TLV s)
  (*prf*) ()

let lemma_serialize_x509_extensions_inner_sequence_TLV_unfold
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (x: x509_extensions_inner_sequence_t_inbound s)
: Lemma ( predicate_serialize_asn1_sequence_TLV_unfold s x )
= lemma_serialize_asn1_sequence_TLV_unfold s x

let lemma_serialize_x509_extensions_inner_sequence_TLV_size
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (x: x509_extensions_inner_sequence_t_inbound s)
: Lemma ( predicate_serialize_asn1_sequence_TLV_size s x )
= lemma_serialize_asn1_sequence_TLV_size s x

let serialize32_x509_extensions_inner_sequence_TLV_backwards
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (#s: serializer p)
  (s32: serializer32_backwards s)
: serializer32_backwards (serialize_x509_extensions_inner_sequence_TLV s)
= coerce_serializer32_backwards
  (* s2  *) (serialize_x509_extensions_inner_sequence_TLV s)
  (* s32 *) (serialize32_asn1_sequence_TLV_backwards
             (* ls *) (s32))
  (* prf *) ()


(* outmost explicit tag*)

let x509_extensions_outmost_explicit_tag: asn1_tag_t
= CUSTOM_TAG CONTEXT_SPECIFIC CONSTRUCTED 3uy

let x509_extensions_t_inbound
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
= inbound_envelop_tag_with_value_of
  (* tag *) x509_extensions_outmost_explicit_tag
  (*  s  *) (serialize_x509_extensions_inner_sequence_TLV s)

let parse_x509_extensions_TLV
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
: parser (parse_asn1_envelop_tag_with_TLV_kind x509_extensions_outmost_explicit_tag) (x509_extensions_t_inbound s)
= x509_extensions_t_inbound s
  `coerce_parser`
  parse_asn1_envelop_tag_with_TLV
  (* tag *) x509_extensions_outmost_explicit_tag
  (*  s  *) (serialize_x509_extensions_inner_sequence_TLV s)

let serialize_x509_extensions_TLV
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
: serializer (parse_x509_extensions_TLV s)
= coerce_parser_serializer
  (* p *) (parse_x509_extensions_TLV s)
  (* s *) (serialize_asn1_envelop_tag_with_TLV
           (* tag *) x509_extensions_outmost_explicit_tag
           (*  s  *) (serialize_x509_extensions_inner_sequence_TLV s))
  (*prf*) ()


let lemma_serialize_x509_extensions_TLV_unfold
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (x: x509_extensions_t_inbound s)
: Lemma ( predicate_serialize_asn1_sequence_TLV_unfold (serialize_x509_extensions_inner_sequence_TLV s) x )
= lemma_serialize_asn1_sequence_TLV_unfold (serialize_x509_extensions_inner_sequence_TLV s) x

let lemma_serialize_x509_extensions_TLV_size
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (x: x509_extensions_t_inbound s)
: Lemma ( predicate_serialize_asn1_sequence_TLV_size (serialize_x509_extensions_inner_sequence_TLV s) x )
= lemma_serialize_asn1_sequence_TLV_size (serialize_x509_extensions_inner_sequence_TLV s) x

let serialize32_x509_extensions_TLV_backwards
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (#s: serializer p)
  (s32: serializer32_backwards s)
: serializer32_backwards (serialize_x509_extensions_TLV s)
= coerce_serializer32_backwards
  (* s2  *) (serialize_x509_extensions_TLV s)
  (* s32 *) (serialize32_asn1_envelop_tag_with_TLV_backwards
             (* tag *) x509_extensions_outmost_explicit_tag
             (* s32 *) (serialize32_x509_extensions_inner_sequence_TLV_backwards s32))
  (* prf *) ()
