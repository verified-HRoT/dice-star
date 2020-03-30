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

(* retuen *) len
