module ASN1.Low.TLV

open ASN1.Base

open ASN1.Spec.Tag
open ASN1.Spec.Length
open ASN1.Spec.BOOLEAN
open ASN1.Spec.NULL
open ASN1.Spec.OCTET_STRING
open ASN1.Spec.TLV

open ASN1.Low.Base
open ASN1.Low.Tag
open ASN1.Low.Length
open ASN1.Low.BOOLEAN
open ASN1.Low.NULL
open ASN1.Low.OCTET_STRING

open LowParse.Low.Base
open LowParse.Low.Combinators
open LowParse.Bytes
open LowParse.Low.DER

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module MB = LowStar.Monotonic.Buffer
module B = LowStar.Buffer
module Cast = FStar.Int.Cast

open FStar.Integers

#reset-options "--max_fuel 0 --max_ifuel 0"

let offset_of_asn1_value
  (value: asn1_value)
: Tot (l: size_t{v l == Seq.length (serialize (serialize_asn1_value (parser_tag_of_asn1_value value)) value)})
= serialize_asn1_value_unfold (parser_tag_of_asn1_value value) value;
  match value with
  | BOOLEAN_VALUE _        -> 1ul
  | NULL_VALUE _           -> 0ul
  | OCTET_STRING_VALUE l s -> u l (* <-- FIXME!*)

#push-options "--query_stats"

#push-options "--z3rlimit 32"
inline_for_extraction
let serialize32_asn1_value_backwards
  (#value_: asn1_value)
: serializer32_backwards (serialize_asn1_value (parser_tag_of_asn1_value value_))
= fun (value: asn1_value_of_TL (parser_tag_of_asn1_value value_))
    (#rrel #rel: _)
    (b: B.mbuffer byte_t rrel rel)
    (pos: size_t)
->  (* Prf *) serialize_asn1_value_unfold (parser_tag_of_asn1_value value) value;
    match value with
    | BOOLEAN_VALUE x        -> ( serialize32_asn1_boolean_backwards ()
                                  (*  x  *) x
                                  (* buf *) b
                                  (* pos *) pos )

    | NULL_VALUE n           -> ( serialize32_asn1_null_backwards ()
                                  (*  x  *) n
                                  (* buf *) b
                                  (* pos *) pos )

    | OCTET_STRING_VALUE l s -> ( serialize32_asn1_octet_string_backwards (u l) (* TODO: `l` should be a machine integer. *)
                                  (*  x  *) s
                                  (* buf *) b
                                  (* pos *) pos)

let serialize32_asn1_TL_backwards ()
: Tot (serializer32_backwards (serialize_TL))
= fun (x: parse_filter_refine filter_TL) (* <-- TODO: Check what's the counterpart of pair in Low*/C. *)
    (#rrel #rel: _)
    (b: B.mbuffer byte_t rrel rel)
    (pos: size_t)
->  let a, len = x in (* <-- TODO: Check KreMLin compat. *)

    (* Prf *) serialize_TL_unfold x;
    (* Prf *) serialize_asn1_length_unfold len;

    let offset_T = offset_of_asn1_tag a in
    let offset_L = offset_of_asn1_length len in

/// serialize ASN.1 DER "Length" `len` backwards into `b[pos - offset_L, pos - 1]`
    let offset_T = offset_of_asn1_tag a in
    let offset_L = offset_of_asn1_length len in

    (* Prf *) let h0 = HST.get () in
    (* Prf *) writable_weaken
              (* buf *) b
              (*range*) (v (pos - offset_L - offset_T)) (v pos)
              (* mem *) h0
              (* from*) (v (pos - offset_L))
              (* to  *) (v pos);
    let _ = serialize32_asn1_length_backwards ()
            (* len *) len
            (* buf *) b
            (* pos *) pos in

/// serialize ASN.1 DER "Tag" `a` backwards into `b[pos - offset_L - offset_T, pos - offset_L - 1]`
    (* Prf *) let h1 = HST.get () in
    (* Prf *) writable_modifies
              (* buf *) b
              (* new *) (v (pos - offset_L - offset_T)) (v (pos))
              (* mem *) h0
              (* loc *) B.loc_none
              (* mem'*) h1;
    (* Prf *) writable_weaken
              (* buf *) b
              (*range*) (v (pos - offset_L - offset_T)) (v pos)
              (* mem *) h1
              (* from*) (v (pos - offset_L - offset_T))
              (* to  *) (v (pos - offset_L));

    let _ = serialize32_asn1_tag_backwards ()
            (* tag *) a
            (* buf *) b
            (* pos *) (pos - offset_L) in

    (* Prf *) let h2 = HST.get () in
    (* Prf *) B.modifies_buffer_from_to_elim
              (* buf *) b
              (*frame*) (pos - offset_L) (pos)
              (* new *) (B.loc_buffer_from_to
                         (* buf *) b
                         (*range*) (pos - offset_L - offset_T) (pos - offset_L))
              (* mem *) h1 h2;
    (* Prf *) B.modifies_buffer_from_to_elim
              (* buf *) b
              (*frame*) 0ul (pos - offset_L - offset_T)
              (* new *) (B.loc_buffer_from_to
                         (* buf *) b
                         (*range*) (pos - offset_L - offset_T) (pos))
              (* mem *) h0 h2;
    (* Prf *) B.modifies_buffer_from_to_elim
              (* buf *) b
              (*frame*) pos (u (B.length b))
              (* new *) (B.loc_buffer_from_to
                         (* buf *) b
                         (*range*) (pos - offset_L - offset_T) (pos))
              (* mem *) h0 h2;
   (* Prf *) writable_modifies
             (* buf *) b
             (* new *) (v (pos - offset_L - offset_T)) (v (pos))
             (* mem *) h0
             (* loc *) B.loc_none
             (* mem'*) h2;

/// return offset
(*return*) (offset_L + offset_T)

let serialize32_asn1_TLV_backwards ()
: Tot (serializer32_backwards serialize_TLV)
= fun (value: asn1_value)
    (#rrel #rel: _)
    (b: B.mbuffer byte_t rrel rel)
    (pos: size_t)
->  let x = parser_tag_of_asn1_value value in
    let a, len = x in
    let offset_V = offset_of_asn1_value value in
    let offset_T = offset_of_asn1_tag a in
    let offset_L = offset_of_asn1_length len in
    (* Prf *) serialize_TLV_unfold value;
    (* Prf *) serialize_TL_unfold x;
    (* Prf *) serialize_asn1_value_unfold x value;
    (* Prf *) let h0 = HST.get () in
    (* Prf *) writable_weaken
              (* buf *) b
              (*range*) (v (pos - offset_V - offset_L - offset_T)) (v pos)
              (* mem *) h0
              (* from*) (v (pos - offset_V))
              (* to  *) (v (pos));
    let offset_V = serialize32_asn1_value_backwards #value
                    (*  x  *) value
                    (* buf *) b
                    (* pos *) pos in
    (* Prf *) let h_V = HST.get () in
    (* Prf *) writable_modifies
              (* buf *) b
              (* new *) (v (pos - offset_V - offset_L - offset_T)) (v (pos))
              (* mem *) h0
              (* loc *) B.loc_none
              (* mem'*) h_V;
    (* Prf *) writable_weaken
              (* buf *) b
              (*range*) (v (pos - offset_V - offset_L - offset_T)) (v (pos))
              (* mem *) h_V
              (* from*) (v (pos - offset_V - offset_L - offset_T))
              (* to  *) (v (pos - offset_V));
    let offset_TL = serialize32_asn1_TL_backwards ()
                    (*  x  *) x
                    (* buf *) b
                    (* pos *) (pos - offset_V) in
    (* Prf *) let h_TLV = HST.get () in
    (* Prf *) B.modifies_buffer_from_to_elim
              (* buf *) b
              (*frame*) (pos - offset_V) (pos)
              (* new *) (B.loc_buffer_from_to
                         (* buf *) b
                         (*range*) (pos - offset_V - offset_L - offset_T) (pos - offset_V))
              (* mem *) h_V h_TLV;
    (* Prf *) B.modifies_buffer_from_to_elim
              (* buf *) b
              (*frame*) 0ul (pos - offset_V - offset_L - offset_T)
              (* new *) (B.loc_buffer_from_to
                         (* buf *) b
                         (*range*) (pos - offset_V - offset_L - offset_T) (pos))
              (* mem *) h0 h_TLV;
    (* Prf *) B.modifies_buffer_from_to_elim
              (* buf *) b
              (*frame*) pos (u (B.length b))
              (* new *) (B.loc_buffer_from_to
                         (* buf *) b
                         (*range*) (pos - offset_V - offset_L - offset_T) (pos))
              (* mem *) h0 h_TLV;
    (* Prf *) writable_modifies
              (* buf *) b
              (* new *) (v (pos - offset_V - offset_L - offset_T)) (v (pos))
              (* mem *) h0
              (* loc *) B.loc_none
              (* mem'*) h_TLV;

(* return *) (offset_V + offset_TL)
#pop-options
