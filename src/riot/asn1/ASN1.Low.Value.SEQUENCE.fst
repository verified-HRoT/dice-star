module ASN1.Low.Value.SEQUENCE
///
/// ASN.1 Low
///
open LowParse.Low.Base

open ASN1.Base
open ASN1.Spec.Tag
open ASN1.Spec.Length
open ASN1.Spec.Value.Envelop
open ASN1.Spec.Value.SEQUENCE
open ASN1.Low.Base
open ASN1.Low.Tag
open ASN1.Low.Length
open ASN1.Low.Value.Envelop

unfold
let serialize32_asn1_sequence_TLV_backwards
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (#s: serializer p)
  (s32: serializer32_backwards s)
: Tot (serializer32_backwards (serialize_asn1_sequence_TLV s))
= serialize32_asn1_envelop_tag_with_TLV_backwards SEQUENCE s32
