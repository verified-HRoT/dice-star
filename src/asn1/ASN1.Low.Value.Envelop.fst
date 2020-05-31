module ASN1.Low.Value.Envelop
///
/// ASN.1 Low
///
open LowParse.Low.Base
open LowParse.Low.Combinators
open LowParse.Low.FLData

open ASN1.Base
open ASN1.Spec.Tag
open ASN1.Spec.Length
open ASN1.Spec.Value.Envelop
open ASN1.Low.Base
open ASN1.Low.Tag
open ASN1.Low.Length

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer
open FStar.Integers

(* NOTE: Read after `ASN1.Spec.Tag`, `ASN1.Spec.Length`, `ASN1.Spec.Value.*` *)

#push-options "--z3rlimit 16"
inline_for_extraction noextract
let serialize32_asn1_envelop_tag_with_TLV_backwards
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (#s: serializer p)
  (a: asn1_type)
  (s32: serializer32_backwards s)
: Tot (serializer32_backwards (serialize_asn1_envelop_tag_with_TLV a s))
= fun x #rrel #rel b pos ->
  (* Prf *) lemma_serialize_asn1_envelop_tag_with_unfold a s (parser_tag_of_asn1_envelop_tag_with a s x) x;
  (* Prf *) lemma_serialize_asn1_envelop_tag_with_TLV_unfold a s x;
  (* Prf *) lemma_serialize_asn1_envelop_tag_with_TLV_size a s x;
  (* Prf *) serialize_tagged_union_eq
            (* st *) (serialize_asn1_tag_of_type a
                      `serialize_nondep_then`
                      serialize_asn1_length_of_type a)
            (* tg *) (parser_tag_of_asn1_envelop_tag_with a s)
            (* s  *) (serialize_asn1_envelop_tag_with_weak a s)
            (* in *) (x);
  (* Prf *) let posl = Ghost.hide (pos - u (Seq.length (serialize (serialize_asn1_envelop_tag_with_TLV a s) x))) in
  (* Prf *) let posr = Ghost.hide pos in

  let offset_data = frame_serializer32_backwards s32 x b posl posr pos in

  let pos = pos - offset_data in

  let offset_tag_len = frame_serializer32_backwards
                       (serialize32_asn1_tag_of_type_backwards a
                        `serialize32_nondep_then_backwards`
                        serialize32_asn1_length_of_type_backwards a)
                       (a, offset_data) b posl posr pos in

(* return *) (offset_tag_len + offset_data)
#pop-options
