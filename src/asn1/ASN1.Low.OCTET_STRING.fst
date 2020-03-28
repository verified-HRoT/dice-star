module ASN1.Low.OCTET_STRING

open ASN1.Base
open ASN1.Spec.OCTET_STRING
open ASN1.Low.Base
open LowParse.Bytes

open FStar.Integers

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module MB = LowStar.Monotonic.Buffer
module B = LowStar.Buffer
module Cast = FStar.Int.Cast

let serialize32_asn1_octet_string
  (len: size_t)
: Tot (serializer32 (serialize_asn1_octet_string (v len)))
= fun (s: lbytes_t (v len))
    (#rrel #rel: _)
    (b: B.mbuffer byte_t rrel rel)
    (pos: size_t)
->  store_seqbytes
    (* src *) s
    (* from*) 0ul
    (* to  *) len
    (* dst *) b
    (* pos *) pos;
(* retuen *) len

let serialize32_asn1_octet_string_backwards
  (len: size_t)
: Tot (serializer32_backwards (serialize_asn1_octet_string (v len)))
= fun (s: lbytes_t (v len))
    (#rrel #rel: _)
    (b: B.mbuffer byte_t rrel rel)
    (pos: size_t)
->  (* Prf *) let h0 = HST.get () in

    store_seqbytes
    (* src *) s
    (* from*) 0ul
    (* to  *) len
    (* dst *) b
    (* pos *) (pos - len);

    (* Prf *) let h1 = HST.get () in
    (* Prf *) B.modifies_buffer_from_to_elim
              (* buf *) b
              (*frame*) 0ul (pos - len)
              (* new *) (B.loc_buffer_from_to
                         (* buf *) b
                         (*range*) (pos - len) (pos))
              (* mem *) h0 h1;
    (* Prf *) B.modifies_buffer_from_to_elim
              (* buf *) b
              (*frame*) pos (u (B.length b))
              (* new *) (B.loc_buffer_from_to
                         (* buf *) b
                         (*range*) (pos - len) (pos))
              (* mem *) h0 h1;
    (* Prf *) writable_modifies
              (* buf *) b
              (* new *) (v (pos - len)) (v (pos))
              (* mem *) h0
              (* loc *) B.loc_none
              (* mem'*) h1;

(* retuen *) len
