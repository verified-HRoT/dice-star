module ASN1.Spec.Value.SEQUENCE

open ASN1.Spec.Base

open ASN1.Base
open ASN1.Spec.Tag
open ASN1.Spec.Length
open ASN1.Spec.Value.Envelop

// let parse_asn1_sequence_TLV #k #t #p s
// = parse_asn1_envelop_tag_with_TLV SEQUENCE s

// let serialize_asn1_sequence_TLV #k #t #p s
// = serialize_asn1_envelop_tag_with_TLV SEQUENCE s

let lemma_serialize_asn1_sequence_TLV_unfold #k #t #p s x
= lemma_serialize_asn1_envelop_tag_with_TLV_unfold SEQUENCE s x

let lemma_serialize_asn1_sequence_TLV_size #k #t #p s x
= lemma_serialize_asn1_envelop_tag_with_TLV_size SEQUENCE s x
