module ASN1.Spec.Value.SEQUENCE

open ASN1.Spec.Base

open ASN1.Base
open ASN1.Spec.Value.Envelop

unfold
let inbound_sequence_value_of
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
= inbound_envelop_tag_with_value_of SEQUENCE s

let parse_asn1_sequence_TLV
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
: parser (parse_asn1_envelop_tag_with_TLV_kind SEQUENCE) (inbound_sequence_value_of s)
= parse_asn1_envelop_tag_with_TLV SEQUENCE s

let serialize_asn1_sequence_TLV
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
: serializer (parse_asn1_sequence_TLV s)
= serialize_asn1_envelop_tag_with_TLV SEQUENCE s

unfold
let predicate_serialize_asn1_sequence_TLV_unfold
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
= predicate_serialize_asn1_envelop_tag_with_TLV_unfold SEQUENCE s

val lemma_serialize_asn1_sequence_TLV_unfold
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (x: inbound_sequence_value_of s)
: Lemma ( predicate_serialize_asn1_sequence_TLV_unfold s x )

unfold
let predicate_serialize_asn1_sequence_TLV_size
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
= predicate_serialize_asn1_envelop_tag_with_TLV_size SEQUENCE s

val lemma_serialize_asn1_sequence_TLV_size
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (x: inbound_sequence_value_of s)
: Lemma ( predicate_serialize_asn1_sequence_TLV_size s x )

unfold noextract
let length_of_asn1_sequence_TLV
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
= length_of_asn1_envelop_tag_with_TLV SEQUENCE s
