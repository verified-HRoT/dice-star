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

#restart-solver
// #push-options "--query_stats --z3rlimit 32 --max_fuel 0 --max_ifuel 0"
let serialize_asn1_TL_backwards ()
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

let serialize32_asn1_TLV_backwards
  (value: asn1_value)
: Tot (serializer32 serialize_TLV)
= fun (value: asn1_value)
    (#rrel #rel: _)
    (b: B.mbuffer byte_t rrel rel)
    (pos: size_t)
->  let x = parser_tag_of_asn1_value value in
    (* Prf *) serialize_TL_unfold x;
    (* Prf *) serialize_asn1_value_unfold x value;
    let offset_TL = serialize_asn1_TL_backwards ()
                    (*  x  *) x
                    (* buf *) b
                    (* pos *) pos in
    let offset_V = serialize32_asn1_value_backwards #value
                    (*  x  *) value
                    (* buf *) b
                    (* pos *) pos in
(* return *) (offset_TL + offset_V)

(*)
/// NOTE: The key is: when should we actually compute the length of value? For primitives,
///       the overhead of compute ahead might be small and we don't need a backward serializer.
/// FIXME: Assumes we have a low-level length computation function at low-level for primitives.
let serialize32_TLV_backwards
  (value: asn1_value)
: serializer32_backwards (serialize_TLV)
= fun (value: asn1_value)
    (#rrel #rel: _)
    (b: B.mbuffer byte_t rrel rel)
    (pos: size_t)
->  (* FIXME: We need a low-level length computation function here. *)
    (* NOTE: Simulating the correct behavior here, we _SHOULDN'T_ know
             the tag and length at this point. *)

/// serialize Value
    let a, offset = parser_tag_of_asn1_value value in
    (* Prf *) serialize_asn1_value_unfold (a, offset) value;
    (* Prf *) assert (v offset == Seq.length (serialize (serialize_asn1_value (a, offset)) value));
    [@inline_let] let gstart_TLV = Ghost.hide (v pos - (Seq.length (serialize serialize_TLV value))) in
    [@inline_let] let gstart = Ghost.hide (v pos - v offset) in
    [@inline_let] let gend   = Ghost.hide (v pos) in
    [@inline_let] let i      = pos -! offset in
    (* Prf *) assert (Ghost.reveal gstart <= v i);
    (* Prf *) let h = HST.get () in
    (* Prf *) writable_weaken
              (* buf *) b
              (*range*) (Ghost.reveal gstart_TLV) (Ghost.reveal gend)
              (* mem *) h
              (* from*) (Ghost.reveal gstart)
              (* to  *) (Ghost.reveal gend);
    let offset = match a with
                 | BOOLEAN      -> ( mbuffer_upd
                                     (* buf *) b
                                     (*start*) gstart
                                     (* end *) gend
                                     (* pos *) i
                                     (*  v  *) (encode_asn1_boolean (BOOLEAN_VALUE?.b value))
                                   ; (* return *) offset )

                 | NULL         -> ( (* return *) offset )

                 | OCTET_STRING -> ( store_bytes
                                     (* src *) (OCTET_STRING_VALUE?.s value)
                                     (* from*) 0ul
                                     (* to  *) offset
                                     (* dst *) b
                                     (* pos *) i
                                   ; (* return *) offset ) in
    (* Prf *) let h' = HST.get () in
    (* Prf *) Seq.lemma_split (Seq.slice (B.as_seq h' b) (Ghost.reveal gstart_TLV) (Ghost.reveal gend)) offset;

/// serialize Length
    (* Prf *) assert ((Ghost.reveal gstart_TLV) <= (v (pos -! offset) - (Seq.length (serialize (serialize_bounded_der_length32 asn1_length_min asn1_length_max) offset))));
    (* Prf *) let h = HST.get () in
    (* Prf *) writable_weaken
              (* buf *) b
              (*range*) (Ghost.reveal gstart_TLV) (Ghost.reveal gend)
              (* mem *) h
              (* from*) (v (pos -! offset) - (Seq.length (serialize (serialize_bounded_der_length32 asn1_length_min asn1_length_max) offset)))
              (* to  *) (v (pos -! offset));
    let offset = offset +! (serialize32_bounded_der_length32_backwards
                            (* min *) asn1_length_min
                            (* max *) asn1_length_max
                            (*  v  *) offset
                            (* dst *) b
                            (* pos *) (pos -! offset)) in
    (* *)
    (* Prf *) let h' = HST.get () in
    (* Prf *) Seq.lemma_split (Seq.slice (B.as_seq h' b) (Ghost.reveal gstart_TLV) (Ghost.reveal gend)) offset;

/// serialize Tag
    (* Prf *) assert ((Ghost.reveal gstart_TLV) <= (v (pos -! offset) - (Seq.length (serialize (serialize_asn1_tag ()) a))));
    (* Prf *) let h = HST.get () in
    (* Prf *) writable_weaken
              (* buf *) b
              (*range*) (Ghost.reveal gstart_TLV) (Ghost.reveal gend)
              (* mem *) h
              (* from*) (v (pos -! offset) - (Seq.length (serialize (serialize_asn1_tag ()) a)))
              (* to  *) (v (pos -! offset));
    let offset = offset +! (serialize32_asn1_tag_backwards ()
                            (*  a  *) a
                            (* dst *) b
                            (* pos *) (pos -! offset)) in

    (* return *) offset


let serialize32_TLV_forwards
  (value: asn1_value)
: serializer32 (serialize_TLV)
= fun (value: asn1_value)
    (#rrel #rel: _)
    (b: B.mbuffer byte_t rrel rel)
    (pos: size_t)
->  (* FIXME: If we want to use this forward serializer, we need
              a low-level implementation for `parser_tag_of_asn1_value`*)
    let a, offset = parser_tag_of_asn1_value value in

admit()
#pop-options
