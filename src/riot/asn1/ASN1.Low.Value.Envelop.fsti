module ASN1.Low.Value.Envelop
///
/// ASN.1 Low
///

open ASN1.Base
open ASN1.Spec.Value.Envelop
open ASN1.Low.Base

(* NOTE: Read after `ASN1.Spec.Tag`, `ASN1.Spec.Length`, `ASN1.Spec.Value.*` *)

inline_for_extraction noextract
val serialize32_asn1_envelop_tag_with_TLV_backwards
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (#s: serializer p)
  (a: asn1_tag_t)
  (s32: serializer32_backwards s)
: (serializer32_backwards (serialize_asn1_envelop_tag_with_TLV a s))
