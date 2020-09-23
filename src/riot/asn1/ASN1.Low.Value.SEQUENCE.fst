module ASN1.Low.Value.SEQUENCE
///
/// ASN.1 Low
///

open ASN1.Spec.Value.SEQUENCE
open ASN1.Low.Value.Envelop

friend ASN1.Spec.Value.SEQUENCE

let serialize32_asn1_sequence_TLV_backwards #k #t #p #s s32
= serialize32_asn1_envelop_tag_with_TLV_backwards SEQUENCE s32
