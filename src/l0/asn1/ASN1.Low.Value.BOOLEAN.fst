module ASN1.Low.Value.BOOLEAN
///
/// ASN.1 Low
///
open LowParse.Low.Base
open LowParse.Low.Combinators
open LowParse.Low.Int

open ASN1.Base
open ASN1.Spec.Value.BOOLEAN
open ASN1.Low.Base

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer
open FStar.Integers

(* NOTE: Read after `ASN1.Spec.Tag`, `ASN1.Spec.Length` *)

friend ASN1.Spec.Value.BOOLEAN

///
/// Encoding a tag into bytes at low-level, implementation of `synth_..._inverse`

///
inline_for_extraction
let encode_asn1_boolean
  (x: bool)
: Tot (b: byte{b == synth_asn1_boolean_inverse x})
= match x with
  | true  -> 0xFFuy
  | false -> 0x00uy

///
/// Low-level function to be used to compute the length of a value's serialization
///
inline_for_extraction
let len_of_asn1_boolean
  (b: bool)
: Tot (l: size_t{
  v l == Seq.length (serialize serialize_asn1_boolean b) /\
  v l == 1})
= lemma_serialize_asn1_boolean_unfold b;
  lemma_serialize_asn1_boolean_size b;
  1ul

///
/// Backwards low-level serializer for ASN1 BOOLEAN values
///
let serialize32_asn1_boolean_backwards ()
= fun (x: bool)
    (#rrel #rel: _)
    (b: B.mbuffer byte rrel rel)
    (pos: size_t)
->  let offset = len_of_asn1_boolean x in
    let content: byte = encode_asn1_boolean x in
    (* Prf *) lemma_serialize_asn1_boolean_unfold x;
    (* Prf *) serialize_u8_spec content;
    mbuffer_upd (* <-- NOTE: serialize the encoding of a BOOLEAN value *)
      (* buf *) b
      (*range*) (v (pos - offset)) (v pos)
      (* pos *) (pos - offset)
      (* val *)content;
(*return*) offset

///
/// Low-level backwards serializer for ASN1 BOOLEAN TLV
///
open ASN1.Spec.Tag
open ASN1.Spec.Length
open ASN1.Low.Tag
open ASN1.Low.Length

///
/// Encode a BOOLEAN value into its TLV tuple, implementation of `synth_..._inverse`
///
inline_for_extraction
let synth_asn1_boolean_TLV_inverse_impl
  (x: datatype_of_asn1_type BOOLEAN)
: Tot (a: ((the_asn1_tag BOOLEAN & asn1_value_int32_of_type BOOLEAN) & datatype_of_asn1_type BOOLEAN){ a == synth_asn1_boolean_TLV_inverse x })
= ((BOOLEAN, 1ul), x)

///
/// Backwards low-level serializer which takes a BOOLEAN value and serializes its TLV tuple.
///
// inline_for_extraction
let serialize32_asn1_boolean_TLV_backwards ()
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

let serialize32_asn1_boolean_TLV_true_backwards ()
= serialize32_asn1_boolean_TLV_backwards ()
  `serialize32_filter_backwards`
  filter_asn1_boolean_true

let serialize32_asn1_boolean_TLV_false_backwards ()
= serialize32_asn1_boolean_TLV_backwards ()
  `serialize32_filter_backwards`
  filter_asn1_boolean_false
