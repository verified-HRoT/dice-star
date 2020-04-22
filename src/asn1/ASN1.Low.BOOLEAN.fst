module ASN1.Low.BOOLEAN
///
/// ASN.1 Low
///
open LowParse.Low.Base
open LowParse.Low.Combinators
open LowParse.Low.Int

open ASN1.Base
open ASN1.Spec.BOOLEAN
open ASN1.Low.Base

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer
open FStar.Integers

let encode_asn1_boolean
  (x: bool)
: Tot (b: byte{b == synth_asn1_boolean_inverse x})
= match x with
  | true  -> 0xFFuy
  | false -> 0x00uy

inline_for_extraction
let len_of_asn1_boolean
  (b: bool)
: Tot (l: size_t{
  v l == Seq.length (serialize serialize_asn1_boolean b) /\
  v l == 1})
= serialize_asn1_boolean_unfold b;
  serialize_asn1_boolean_size b;
  1ul

inline_for_extraction
let serialize32_asn1_boolean_backwards ()
: Tot (serializer32_backwards serialize_asn1_boolean)
= fun (x: bool)
    (#rrel #rel: _)
    (b: B.mbuffer byte rrel rel)
    (pos: size_t)
->  let offset = len_of_asn1_boolean x in
    let content: byte = encode_asn1_boolean x in
    (* Prf *) serialize_asn1_boolean_unfold x;
    (* Prf *) serialize_u8_spec content;
    mbuffer_upd
      (* buf *) b
      (*range*) (v (pos - offset)) (v pos)
      (* pos *) (pos - offset)
      (* val *)content;
(*return*) offset

open ASN1.Spec.Tag
open ASN1.Spec.Length
open ASN1.Low.Tag
open ASN1.Low.Length

inline_for_extraction
let synth_asn1_boolean_TLV_inverse_impl
  (x: datatype_of_asn1_type BOOLEAN)
: Tot (a: ((the_asn1_type BOOLEAN & asn1_int32_of_type BOOLEAN) & datatype_of_asn1_type BOOLEAN){a == synth_asn1_boolean_TLV_inverse x})
= ((BOOLEAN, 1ul), x)

inline_for_extraction
let serialize32_asn1_boolean_TLV_backwards ()
: Tot (serializer32_backwards serialize_asn1_boolean_TLV)
= serialize32_synth_backwards
  (* ls1*) (serialize32_asn1_tag_of_type_backwards BOOLEAN
           `serialize32_nondep_then_backwards`
           serialize32_asn1_length_of_type_backwards BOOLEAN
           `serialize32_nondep_then_backwards`
           serialize32_asn1_boolean_backwards ())
  (* f2 *) (synth_asn1_boolean_TLV)
  (* g1 *) (synth_asn1_boolean_TLV_inverse)
  (* lg1*) (synth_asn1_boolean_TLV_inverse_impl)
  (* Prf*) ()
