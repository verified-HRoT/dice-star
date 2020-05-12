module ASN1.Low.Value.SEQUENCE
///
/// ASN.1 Low
///
open LowParse.Low.Base
open LowParse.Low.Combinators
open LowParse.Low.FLData

open ASN1.Base
open ASN1.Spec.Value.SEQUENCE
open ASN1.Low.Base
open ASN1.Low.Tag
open ASN1.Low.Length

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer
open FStar.Integers

(* NOTE: Read after `ASN1.Spec.Tag`, `ASN1.Spec.Length`, `ASN1.Spec.Value.*` *)

#push-options "--z3rlimit 16"
inline_for_extraction
let len_of_sequence_TLV
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (len_of_value:
    (value: t {asn1_value_length_inbound_of_type SEQUENCE (Seq.length (serialize s value))})
    -> Tot (len: asn1_value_int32_of_type SEQUENCE {v len == Seq.length (serialize s value)}))
  (value: t{ asn1_value_length_inbound_of_type SEQUENCE (Seq.length (serialize s value)) })
: Tot (len: asn1_TLV_int32_of_type SEQUENCE {
            v len == length_of_sequence_TLV s value /\
            (* NOTE: This _SHOULD_ be implied by the proposition above? *)
            v len == Seq.length (serialize (serialize_asn1_sequence_TLV s) value)
            })
= [@inline_let]
  let len = len_of_value value in
  1ul + len_of_asn1_length len + len
#pop-options

inline_for_extraction noextract
let serialize32_fldata_strong_backwards
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (#s: serializer p)
  (ls: serializer32_backwards s)
  (len: asn1_int32)
: Tot (serializer32_backwards (serialize_fldata_strong s (v len)))
= fun (x: parse_fldata_strong_t s (v len))
-> ls x

inline_for_extraction
let parser_tag_of_asn1_sequence_impl
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (len_of_data:
    (data: t { asn1_value_length_inbound_of_type SEQUENCE (Seq.length (serialize s data)) })
    -> Tot (len: asn1_value_int32_of_type SEQUENCE { v len == Seq.length (serialize s data) }))
  (data: t { asn1_value_length_inbound_of_type SEQUENCE (Seq.length (serialize s data)) } )
: Tot (tag: (the_asn1_type SEQUENCE & asn1_value_int32_of_type SEQUENCE) { tag == parser_tag_of_asn1_sequence s data })
= (SEQUENCE, len_of_data data)

inline_for_extraction
let synth_asn1_sequence_value_inverse_impl
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (tag: (the_asn1_type SEQUENCE & asn1_value_int32_of_type SEQUENCE))
  (data: refine_with_tag (parser_tag_of_asn1_sequence s) tag)
: Tot (y: parse_fldata_strong_t s (v (snd tag)){ y == synth_asn1_sequence_value_inverse s tag data })
= data <: refine_with_tag (parser_tag_of_asn1_sequence s) tag

inline_for_extraction
let serialize32_asn1_sequence_TLV_backwards
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (#s: serializer p)
  (ls: serializer32_backwards s)
  (len_of_data:
    (data: t { asn1_value_length_inbound_of_type SEQUENCE (Seq.length (serialize s data)) })
    -> Tot (len: asn1_value_int32_of_type SEQUENCE { v len == Seq.length (serialize s data) }))
: Tot (serializer32_backwards (serialize_asn1_sequence_TLV s))
= serialize32_tagged_union_backwards
  (* lst *) (serialize32_asn1_tag_of_type_backwards SEQUENCE
             `serialize32_nondep_then_backwards`
             serialize32_asn1_length_of_type_backwards SEQUENCE)
  (* tag *) (parser_tag_of_asn1_sequence_impl s len_of_data)
  (* s32 *) (fun (tag: the_asn1_type SEQUENCE & asn1_value_int32_of_type SEQUENCE)
             -> [@inline_let]
               let len = snd tag in
               //let SEQUENCE, len = tag in
                (weak_kind_of_type SEQUENCE
                 `serialize32_weaken_backwards`
                (serialize32_synth_backwards
                 (* ls1 *) (serialize32_fldata_strong_backwards ls len)
                 (* f2  *) (synth_asn1_sequence_value s tag)
                 (* g1  *) (synth_asn1_sequence_value_inverse s tag)
                 (* g1' *) (synth_asn1_sequence_value_inverse_impl s tag)
                 (* prf *) ())) <: serializer32_backwards (serialize_asn1_sequence_value_weak s tag))
