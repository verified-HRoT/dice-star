module ASN1.Low.Value.BigInteger

open ASN1.Base
open ASN1.Low.Base
open ASN1.Low.Tag
open ASN1.Low.Length
open ASN1.Low.Value.OCTET_STRING
open ASN1.Low.Bytes32
open ASN1.Spec.Value.BigInteger
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module MB = LowStar.Monotonic.Buffer
module B = LowStar.Buffer
module Cast = FStar.Int.Cast
open LowParse.Low.Bytes

open FStar.Integers
module B32 = FStar.Bytes

friend ASN1.Spec.Value.BigInteger

#set-options "--z3rlimit 32 --ifuel 0 --ifuel 0"

// let serialize32_asn1_length_of_big_integer_backwards
// : serializer32_backwards (serialize_asn1_length_of_big_integer)
// = serialize32_asn1_length_of_bound_backwards 1ul (asn1_int32_max - 6ul)

inline_for_extraction
let serialize32_big_integer_as_octet_string_backwards len
= fun (x)
    (#rrel #rel: _)
    (b: B.mbuffer byte rrel rel)
    (pos: size_t)
->  (* prf *) let h0 = HST.get () in
    (* Prf *) lemma_serialize_big_integer_as_octet_string_unfold len (x);
    (* Prf *) writable_weaken
              (* buf *) b
              (*range*) (v (pos - len)) (v pos)
              (* mem *) h0
              (* from*) (v (pos - x.ASN1.Base.len))
              (* to  *) (v pos);
    store_bytes
      (* src *) (x.s)
      (* from*) 0ul
      (* to  *) (x.ASN1.Base.len)
      (* dst *) b
      (* pos *) (pos - (x.ASN1.Base.len));

    if (B32.get (x.s) 0ul >= 0x80uy) then
    ( let h1 = HST.get () in
      (* Prf *) writable_modifies
                (* buf *) b
                (*range*) (v (pos - len)) (v pos)
                (* mem *) h0
                (*other*) B.loc_none
                (* mem'*) h1;
      (* Prf *) writable_weaken
                (* buf *) b
                (*range*) (v (pos - len)) (v pos)
                (* mem *) h1
                (* from*) (v (pos - len))
                (* to  *) (v (pos - x.ASN1.Base.len));
      mbuffer_upd
        (* buf *) b
        (*range*) (v (pos - len)) (v pos)
        (* pos *) (pos - len)
        (* val *) 0x00uy;
      (* Prf *) let h2 = HST.get () in
      (* Prf *) B.modifies_buffer_from_to_elim
            (* buf *) b
            (*frame*) (pos - x.ASN1.Base.len) (pos)
            (* new *) (B.loc_buffer_from_to b (pos - len) (pos - x.ASN1.Base.len))
            (* mem *) h1
            (* mem'*) h2;
  (* Prf *) Seq.lemma_split (Seq.slice (B.as_seq h2 b) (v (pos - len)) (v pos)) 1 );

(* retuen *) len

// noextract inline_for_extraction
// let parser_tag_of_big_integer_as_octet_string_impl
//   (x: big_integer_as_octet_string_t)
// : Tot (tg: (the_asn1_tag INTEGER & asn1_value_int32_of_big_integer)
//            { tg == parser_tag_of_big_integer_as_octet_string x })
// = let (.[]) = B32.index in
//   if ((dsnd x).[0] >= 0x80uy) then
//   ( (INTEGER, dfst x + 1ul) )
//   else
//   ( (INTEGER, dfst x) )

let serialize32_big_integer_as_octet_string_TLV_backwards ()
= serialize32_tagged_union_backwards
  (* lst *) (serialize32_asn1_tag_of_type_backwards INTEGER
             `serialize32_nondep_then_backwards`
             serialize32_asn1_length_of_big_integer_backwards)
  (* ltg *) (parser_tag_of_big_integer_as_octet_string_impl)
  (* ls  *) (fun parser_tag -> (serialize32_synth_backwards
                              (* ls *) (weak_kind_of_big_integer
                                        `serialize32_weaken_backwards`
                                        serialize32_big_integer_as_octet_string_backwards (msnd parser_tag))
                              (* f2 *) (synth_big_integer_as_octet_string_V parser_tag)
                              (* g1 *) (synth_big_integer_as_octet_string_V_inverse parser_tag)
                              (* g1'*) (synth_big_integer_as_octet_string_V_inverse parser_tag)
                              (* prf*) ()))

