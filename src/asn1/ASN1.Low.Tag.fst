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

///
/// Encode ASN1 tag to a byte, implementation of `synth_asn1_tag_inverse`
///
let encode_asn1_tag
  (a: asn1_type)
: Tot (b: byte{b == synth_asn1_tag_inverse a})
= match a with
  | BOOLEAN      -> 0x01uy
  | INTEGER      -> 0x02uy
  | BIT_STRING   -> 0x03uy
  | OCTET_STRING -> 0x04uy
  | NULL         -> 0x05uy
  | OID          -> 0x06uy
  | SEQUENCE     -> 0x30uy

///
/// Low-level implemenation of ASN1 Tag's length computation function
///
let len_of_asn1_tag
  (tag: asn1_type)
: Tot (l: size_t{
  v l == Seq.length (serialize serialize_asn1_tag tag) /\
  v l == 1})
= (* Prf *) serialize_asn1_tag_unfold tag;
  (* Prf *) serialize_asn1_tag_size tag;
  1ul

///
/// Backwards low-level serializer for asn1 tags
///
inline_for_extraction
let serialize32_asn1_tag_backwards ()
: Tot (serializer32_backwards serialize_asn1_tag)
= fun (a: asn1_type)
    (#rrel #rel: _)
    (b: B.mbuffer byte rrel rel)
    (pos: size_t)
->  let offset = len_of_asn1_tag a in
    let content: byte = encode_asn1_tag a in
    (* Prf *) serialize_asn1_tag_unfold a;
    (* Prf *) serialize_u8_spec content;
    mbuffer_upd (* <-- NOTE: serialize the encoding of the ASN1 Tag *)
      (* buf *) b
      (*range*) (v (pos - offset)) (v pos)
      (* pos *) (pos - offset)
      (* val *) content;
(*return*) offset


///
/// Backwards low-level serializer for a specific asn1 tag
///
inline_for_extraction
let serialize32_asn1_tag_of_type_backwards
  (_a: asn1_type)
: Tot (serializer32_backwards (serialize_asn1_tag_of_type _a))
= fun (a: the_asn1_type _a)
    (#rrel #rel: _)
    (b: B.mbuffer byte rrel rel)
    (pos: size_t)
->  let offset = len_of_asn1_tag a in
    let content: byte = encode_asn1_tag a in
    (* Prf *) serialize_asn1_tag_of_type_unfold _a a;
    (* Prf *) serialize_u8_spec content;
    mbuffer_upd (* <-- NOTE: serialize the encoding of the ASN1 Tag *)
      (* buf *) b
      (*range*) (v (pos - offset)) (v pos)
      (* pos *) (pos - offset)
      (* val *) content;
(*return*) offset
