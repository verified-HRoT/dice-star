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
inline_for_extraction
let encode_asn1_tag
  (a: asn1_tag_t)
: Tot (b: byte{b == synth_asn1_tag_inverse a})
= match a with
  | BOOLEAN      -> 0x01uy
  | INTEGER      -> 0x02uy
  | BIT_STRING   -> 0x03uy
  | OCTET_STRING -> 0x04uy
  | ASN1_NULL         -> 0x05uy
  | OID          -> 0x06uy
  | SEQUENCE     -> 0x30uy
  | CUSTOM_TAG tag_class tag_form tag_value -> ( let b_tag_class = match tag_class with
                                                                     | APPLICATION      -> 0b01000000uy
                                                                     | CONTEXT_SPECIFIC -> 0b10000000uy
                                                                     | PRIVATE          -> 0b11000000uy in
                                                   let b_tag_form  = match tag_form with
                                                                     | PRIMITIVE   -> 0b000000uy
                                                                     | CONSTRUCTED -> 0b100000uy in
                                                   b_tag_class + b_tag_form + tag_value )

///
/// Low-level implemenation of ASN1 Tag's length computation function

///
inline_for_extraction
let len_of_asn1_tag
  (tag: asn1_tag_t)
: Tot (l: size_t{
  v l == Seq.length (serialize serialize_asn1_tag tag) /\
  v l == 1})
= (* Prf *) lemma_serialize_asn1_tag_unfold tag;
  (* Prf *) lemma_serialize_asn1_tag_size tag;
  1ul

#set-options "--z3rlimit 32"

///
/// Backwards low-level serializer for asn1 tags
///
inline_for_extraction
let serialize32_asn1_tag_backwards ()
: Tot (serializer32_backwards serialize_asn1_tag)
= fun (a: asn1_tag_t)
    (#rrel #rel: _)
    (b: B.mbuffer byte rrel rel)
    (pos: size_t)
->  let offset = len_of_asn1_tag a in
    let content: byte = encode_asn1_tag a in
    (* Prf *) lemma_serialize_asn1_tag_unfold a;
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
inline_for_extraction noextract
let serialize32_asn1_tag_of_type_backwards
  (_a: asn1_tag_t)
: Tot (serializer32_backwards (serialize_asn1_tag_of_type _a))
= fun a
    #rrel #rel
    b
    pos
->  let offset = len_of_asn1_tag a in
   let content: byte = encode_asn1_tag a in
    (* Prf *) lemma_serialize_asn1_tag_of_type_unfold _a a;
    (* Prf *) serialize_u8_spec content;
    mbuffer_upd (* <-- NOTE: serialize the encoding of the ASN1 Tag *)
      (* buf *) b
      (*range*) (v (pos - offset)) (v pos)
      (* pos *) (pos - offset)
      (* val *) content;
(*return*) offset
