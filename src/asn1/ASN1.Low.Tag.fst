module ASN1.Low.Tag
///
/// ASN.1 Low
///
open LowParse.Low.Base
open LowParse.Low.Combinators
open LowParse.Low.Int

open ASN1.Base
open ASN1.Spec.Tag
open ASN1.Low.Base

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer
open FStar.Integers

let encode_asn1_tag
  (a: asn1_type)
: Tot (b: byte{b == synth_asn1_tag_inverse a})
= match a with
  | BOOLEAN      -> 0x01uy
  | OCTET_STRING -> 0x04uy
  | NULL         -> 0x05uy
  | SEQUENCE     -> 0x30uy

let offset_of_asn1_tag
  (tag: asn1_type)
: Tot (l: size_t{v l == Seq.length (serialize serialize_asn1_tag tag)})
= 1ul

inline_for_extraction
let serialize32_asn1_tag_backwards ()
: Tot (serializer32_backwards serialize_asn1_tag)
= fun (a: asn1_type)
    (#rrel #rel: _)
    (b: B.mbuffer byte_t rrel rel)
    (pos: size_t)
->  let offset = offset_of_asn1_tag a in
    let content: byte_t = encode_asn1_tag a in
    (* Prf *) serialize_asn1_tag_unfold a;
    (* Prf *) serialize_u8_spec content;
    mbuffer_upd b (v (pos - offset)) (v pos) (pos - offset) content;
    offset

inline_for_extraction
let serialize32_the_asn1_tag_backwards
  (_a: asn1_type)
: Tot (serializer32_backwards (serialize_the_asn1_tag _a))
= fun (a: the_asn1_type _a)
    (#rrel #rel: _)
    (b: B.mbuffer byte_t rrel rel)
    (pos: size_t)
->  let offset = offset_of_asn1_tag a in
    let content: byte_t = encode_asn1_tag a in
    (* Prf *) serialize_the_asn1_tag_unfold _a a;
    (* Prf *) serialize_u8_spec content;
    mbuffer_upd b (v (pos - offset)) (v pos) (pos - offset) content;
    offset
