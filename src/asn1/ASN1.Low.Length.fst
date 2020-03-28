module ASN1.Low.Length
///
/// ASN.1 Low
///
open LowParse.Low.Base
open LowParse.Low.Combinators
module LDER = LowParse.Low.DER
module SDER = LowParse.Spec.DER

open ASN1.Base
open ASN1.Spec.Length
open ASN1.Low.Base

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer
open FStar.Integers

#reset-options "--max_fuel 0 --max_ifuel 0"

#push-options "--z3rlimit 16"
let offset_of_asn1_length
  (len: asn1_int32)
: Pure (offset: size_t{v offset == Seq.length (serialize serialize_asn1_length len)})
  (requires True)
  (ensures fun offset -> v offset == Seq.length (serialize serialize_asn1_length len))
= serialize_asn1_length_unfold len;
  let x = SDER.tag_of_der_length32_impl len in
  if x < 128uy then
  ( 1ul )
  else if x = 129uy then
  ( 2ul )
  else if x = 130uy then
  ( 3ul )
  else if x = 131uy then
  ( 4ul )
  else
  ( 5ul )
#pop-options

let serialize32_asn1_length ()
: Tot (serializer32 serialize_asn1_length)
= LDER.serialize32_bounded_der_length32 asn1_length_min asn1_length_max

#push-options "--z3rlimit 32"
let serialize32_asn1_length_backwards ()
: Tot (serializer32_backwards serialize_asn1_length)
= fun (len: asn1_int32)
    (#rrel #rel: _)
    (b: B.mbuffer byte_t rrel rel)
    (pos: size_t)
-> let offset = offset_of_asn1_length len in
   (* Prf *) let h0 = HST.get () in
   let offset = serialize32_asn1_length () len b (pos - offset) in
   (* Prf *) let h1 = HST.get () in
   (* Prf *) B.modifies_buffer_from_to_elim
             (* buf *) b
             (*frame*) 0ul (pos - offset)
             (* new *) (B.loc_buffer_from_to
                        (* buf *) b
                        (*range*) (pos - offset) (pos))
             (* mem *) h0 h1;
   (* Prf *) B.modifies_buffer_from_to_elim
             (* buf *) b
             (*frame*) pos (u (B.length b))
             (* new *) (B.loc_buffer_from_to
                        (* buf *) b
                        (*range*) (pos - offset) (pos))
             (* mem *) h0 h1;
   (* Prf *) writable_modifies
             (* buf *) b
             (* new *) (v (pos - offset)) (v (pos))
             (* mem *) h0
             (* loc *) B.loc_none
             (* mem'*) h1;
(* return *) offset
#pop-options
