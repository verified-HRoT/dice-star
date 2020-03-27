module ASN1.Low.TLV

open ASN1.Base
open ASN1.Spec.Tag
friend ASN1.Spec.Tag
open ASN1.Spec.BOOLEAN
friend ASN1.Spec.BOOLEAN
open ASN1.Spec.NULL
open ASN1.Spec.TLV

// open ASN1.Low.BOOLEAN
// friend ASN1.Low.BOOLEAN

include LowParse.Low.Base
include LowParse.Low.Combinators
include LowParse.Bytes
include LowParse.Low.DER
// include LowParse.Low.SeqBytes

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module MB = LowStar.Monotonic.Buffer
module B = LowStar.Buffer
module Cast = FStar.Int.Cast
// open Lib.IntTypes
open FStar.Integers

#push-options "--z3rlimit 32"
let size_t = U32.t
let byte_t = U8.t

/// NOTE: Adapted from `LowParse.Low.Bytes.store_bytes`
/// TODO: Ensure writable
inline_for_extraction
let store_seqbytes
  (src: bytes)
  (src_from src_to: size_t)
  (#rrel #rel: _)
  (dst: B.mbuffer byte_t rrel rel)
  (dst_pos: size_t)
: HST.Stack unit
  (requires (fun h ->
    B.live h dst /\
    U32.v src_from <= U32.v src_to /\ U32.v src_to <= Seq.length src /\
    U32.v dst_pos + (U32.v src_to - U32.v src_from) <= B.length dst /\
    writable dst (U32.v dst_pos) (U32.v dst_pos + (U32.v src_to - U32.v src_from)) h
  ))
  (ensures (fun h _ h' ->
    B.modifies (B.loc_buffer_from_to dst dst_pos (dst_pos `U32.add` (src_to `U32.sub` src_from))) h h' /\
    Seq.slice (B.as_seq h' dst) (U32.v dst_pos) (U32.v dst_pos + (U32.v src_to - U32.v src_from)) == Seq.slice (src) (U32.v src_from) (U32.v src_to)
  ))
= let h0 = HST.get () in
  HST.push_frame ();
  let h1 = HST.get () in
  let bi = B.alloca 0ul 1ul in
  let h2 = HST.get () in
  let len = src_to `U32.sub` src_from in
  C.Loops.do_while
    (fun h stop ->
      B.modifies (B.loc_union (B.loc_region_only true (HS.get_tip h1)) (B.loc_buffer_from_to dst dst_pos (dst_pos `U32.add` len))) h2 h /\
      B.live h bi /\ (
      let i = Seq.index (B.as_seq h bi) 0 in
      U32.v i <= U32.v len /\
      writable dst (U32.v dst_pos) (U32.v dst_pos + U32.v len) h /\
      Seq.slice (B.as_seq h dst) (U32.v dst_pos) (U32.v dst_pos + U32.v i) `Seq.equal` Seq.slice (src) (U32.v src_from) (U32.v src_from + U32.v i) /\
      (stop == true ==> i == len)
    ))
    (fun _ ->
      let i = B.index bi 0ul in
      if i = len
      then true
      else begin
        let x = Seq.index src (v src_from + v i) in
        mbuffer_upd dst (Ghost.hide (U32.v dst_pos)) (Ghost.hide (U32.v dst_pos + U32.v len)) (dst_pos `U32.add` i) x;
        let i' = i `U32.add` 1ul in
        B.upd bi 0ul i';
        let h' = HST.get () in
        Seq.lemma_split (Seq.slice (B.as_seq h' dst) (U32.v dst_pos) (U32.v dst_pos + U32.v i')) (U32.v i);
        i' = len
      end
    )
    ;
  HST.pop_frame ()

#pop-options

#push-options "--z3rlimit 64"

// [@unifier_hint_injective]
// inline_for_extraction
// let serializer32_backwards
//   (#k: parser_kind)
//   (#t: Type)
//   (#p: parser k t)
//   (s: serializer p)
// : Tot Type
// = (x: t) ->
//   (#rrel: _) -> (#rel: _) ->
//   (b: B.mbuffer byte_t rrel rel) ->
//   (pos: size_t) ->
//   HST.Stack (offset: size_t)
//   (* NOTE: b[pos - offset] is not written and b[pos - offset + 1] ~ b[pos] are written.
//            Which means `offset` could at most be `pos + 1`?*)
//   (requires fun h ->
//     let offset = Seq.length (serialize s x) in
//     B.live h b /\
//     (* NOTE: 1) a valid `pos` should be in range [0, |b|),
//              2) a valid `offset` should be in range [0, pos + 1],
//              3) the slice gonna to be written is b[pos - offset + 1, pos]. *)
//     0 <= v pos /\ v pos < B.length b /\
//     0 <= offset /\ offset <= v pos + 1 /\
//     writable
//     (* buf *) b
//     (* from*) (v pos - offset + 1)
//     (* exto*) (v pos + 1)
//     (* mem *) h)
//   (ensures fun h offset h' ->
//     let sx = serialize s x in
//     Seq.length sx == v offset /\
//     B.modifies (B.loc_buffer_from_to b (pos - offset + 1) (pos + 1)) h h' /\
//     B.live h b /\
//     Seq.slice (B.as_seq h' b) (v pos - v offset) (v pos) `Seq.equal` sx)

[@unifier_hint_injective]
inline_for_extraction
let serializer32_backwards
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
: Tot Type
= (x: t) ->
  (#rrel: _) -> (#rel: _) ->
  (b: B.mbuffer byte_t rrel rel) ->
  (pos: size_t) ->
  HST.Stack (offset: size_t)
  (* NOTE: b[pos] is already written, and b[pos - offset, pos - 1] will be written. *)
  (requires fun h ->
    let offset = Seq.length (serialize s x) in
    B.live h b /\
    offset <= v pos /\ v pos <= B.length b /\
    writable b (v pos - offset) (v pos) h)
  (ensures fun h offset h' ->
    let sx = serialize s x in
    Seq.length sx == v offset /\
    B.modifies (B.loc_buffer_from_to b (pos - offset) (pos)) h h' /\
    // (forall (i:nat{0 <= i /\ i < B.length b /\ (i < v (pos - offset) \/ v pos <= i)}).
    //   let s0 = B.as_seq h b in
    //   let s1 = B.as_seq h' b in
    //   s0.[i] == s1.[i]) /\
    B.live h b /\
    Seq.slice (B.as_seq h' b) (v pos - v offset) (v pos) `Seq.equal` sx)

/// NOTE: Inlining all low-level serializers for now
inline_for_extraction
let serialize32_asn1_value_backwards'
  (x: valid_asn1_TL) (* FIXME: I doubt if we could know this ahead. *)
: serializer32_backwards (serialize_asn1_value x)
= fun (value: asn1_value_of_TL x)
    (#rrel #rel: _)
    (b: B.mbuffer byte_t rrel rel)
    (pos: size_t)
->  let a, offset = x in
    (* Prf *) serialize_asn1_value_unfold x value;
    (* Prf *) assert (v offset == Seq.length (serialize (serialize_asn1_value x) value));
    [@inline_let] let gstart = Ghost.hide (v (pos - offset)) in
    [@inline_let] let gend   = Ghost.hide (v pos) in
    [@inline_let] let i      = pos - offset in
    // (* Prf *) assert (Ghost.reveal gstart <= v i);
    match a with
    | BOOLEAN      -> ( mbuffer_upd
                        (* buf *) b
                        (*start*) gstart
                        (* end *) gend
                        (* pos *) i
                        (*  v  *) (encode_asn1_boolean (BOOLEAN_VALUE?.b value))
                      ; (* return *) offset )

    | NULL         -> ( (* return *) offset )

    | OCTET_STRING -> ( store_seqbytes
                        (* src *) (OCTET_STRING_VALUE?.s value)
                        (* from*) 0ul
                        (* to  *) offset
                        (* dst *) b
                        (* pos *) i
                      ; (* return *) offset )

let offset_of_asn1_value
  (value: asn1_value)
: Tot (l: size_t{v l == Seq.length (serialize (serialize_asn1_value (parser_tag_of_asn1_value value)) value)})
= serialize_asn1_value_unfold (parser_tag_of_asn1_value value) value;
  match value with
  | BOOLEAN_VALUE _        -> 1ul
  | NULL_VALUE _           -> 0ul
  | OCTET_STRING_VALUE l s -> u l (* <-- FIXME!*)

let offset_of_asn1_tag
  (tag: asn1_type)
: Tot (l: size_t{v l == Seq.length (serialize (serialize_asn1_tag ()) tag)})
= 1ul (* <-- Maybe FIXME *)

inline_for_extraction
let serialize32_asn1_value_backwards
  (#value_: asn1_value)
: serializer32_backwards (serialize_asn1_value (parser_tag_of_asn1_value value_))
= fun (value: asn1_value_of_TL (parser_tag_of_asn1_value value_))
    (#rrel #rel: _)
    (b: B.mbuffer byte_t rrel rel)
    (pos: size_t)
->  let offset = offset_of_asn1_value value in
    (* Prf *) serialize_asn1_value_unfold (parser_tag_of_asn1_value value) value;
    (* Prf *) assert (v offset == Seq.length (serialize (serialize_asn1_value (parser_tag_of_asn1_value value)) value));
    [@inline_let] let gstart = Ghost.hide (v (pos - offset)) in
    [@inline_let] let gend   = Ghost.hide (v pos) in
    let i      = pos - offset in
    // (* Prf *) assert (Ghost.reveal gstart <= v i);
    match value with
    | BOOLEAN_VALUE x        -> ( mbuffer_upd
                                  (* buf *) b
                                  (*start*) gstart
                                  (* end *) gend
                                  (* pos *) i
                                  (*  v  *) (encode_asn1_boolean x)
                                ; (* return *) offset )

    | NULL_VALUE n           -> ( (* return *) offset )

    | OCTET_STRING_VALUE l s -> ( store_seqbytes
                                  (* src *) s
                                  (* from*) 0ul
                                  (* to  *) offset
                                  (* dst *) b
                                  (* pos *) i
                                ; (* return *) offset )

/// NOTE: A simple workaround to get the length of a der `len` before serializing it, then just use
///       the exist forward serializer, instead of re-impl a backward serializer.
let offset_of_bounded_der_length32
  (min: der_length_t)
  (max: der_length_t { min <= max /\ max < 4294967296 } )
  (y' : bounded_int32 (min) (max))
: Pure (l: size_t{U32.v l == Seq.length (serialize (serialize_bounded_der_length32 (min) (max)) y')})
  (requires True)
  (ensures fun l -> U32.v l == Seq.length (serialize (serialize_bounded_der_length32 (min) (max)) y'))
= serialize_bounded_der_length32_unfold (min) (max) y';
  let x = tag_of_der_length32_impl y' in
  if x `U8.lt` 128uy then
  ( 1ul )
  else if x = 129uy then
  ( 2ul )
  else if x = 130uy then
  ( 3ul )
  else if x = 131uy then
  ( 4ul )
  else
  ( 5ul )

/// NOTE: Backward version of `LowParse.Low.DER.serialize32_bounded_der_length32`
let serialize32_bounded_der_length32_backwards
  (min: der_length_t)
  (max: der_length_t { min <= max /\ max < 4294967296 } )
: Tot (serializer32_backwards (serialize_bounded_der_length32 min max))
= fun (y' : bounded_int32 (min) (max))
    (#rrel #rel: _)
    (b: B.mbuffer byte_t rrel rel)
    (pos: size_t)
-> let offset = offset_of_bounded_der_length32 min max y' in
   serialize32_bounded_der_length32' min max y' b (pos - offset)

let serialize32_asn1_tag_backwards ()
: Tot (serializer32_backwards (serialize_asn1_tag ()))
= fun (a: asn1_type)
    (#rrel #rel: _)
    (b: B.mbuffer byte_t rrel rel)
    (pos: size_t)
->  let offset = offset_of_asn1_tag a in
    let content: byte_t = encode_asn1_tag a in
    mbuffer_upd b (Ghost.hide (v (pos - offset))) (Ghost.hide (v pos)) (pos - offset) content;
    offset

#restart-solver
// #push-options "--query_stats --z3rlimit 32 --max_fuel 0 --max_ifuel 0"
let serialize_TL_backwards ()
: Tot (serializer32_backwards (serialize_TL))
= fun (x: parse_filter_refine filter_TL) (* <-- TODO: Check what's the counterpart of pair in Low*/C. *)
    (#rrel #rel: _)
    (b: B.mbuffer byte_t rrel rel)
    (pos: size_t)
->  let a, len = x in (* <-- TODO: Check KreMLin compat. *)

    (* Prf *) serialize_TL_unfold x;
    (* Prf *) serialize_bounded_der_length32_unfold asn1_length_min asn1_length_max len;

    let offset_T = offset_of_asn1_tag a in
    let offset_L = offset_of_bounded_der_length32 asn1_length_min asn1_length_max len in

/// serialize ASN.1 DER "Length" `len` backwards into `b[pos - offset_L, pos - 1]`
    let offset_T = offset_of_asn1_tag a in
    let offset_L = offset_of_bounded_der_length32 asn1_length_min asn1_length_max len in

    (* Prf *) let h0 = HST.get () in
    (* Prf *) writable_weaken
              (* buf *) b
              (*range*) (v (pos - offset_L - offset_T)) (v pos)
              (* mem *) h0
              (* from*) (v (pos - offset_L))
              (* to  *) (v pos);
    (* Prf *) writable_weaken
              (* buf *) b
              (*range*) (v (pos - offset_L - offset_T)) (v pos)
              (* mem *) h0
              (* from*) (v (pos - offset_L - offset_T))
              (* to  *) (v (pos - offset_L));
    let _ = serialize32_bounded_der_length32_backwards
            (* min *) asn1_length_min
            (* max *) asn1_length_max
            (* len *) len
            (* buf *) b
            (* pos *) pos in

/// serialize ASN.1 DER "Tag" `a` backwards into `b[pos - offset_L - offset_T, pos - offset_L - 1]`
    (* Prf *) let h1 = HST.get () in
    (* Prf *) assert (B.modifies (B.loc_buffer_from_to b (pos - offset_L) (pos)) h0 h1);
    (* NOTE: Need to prove the frame. *)
    (* Prf *) B.modifies_buffer_from_to_elim
              (* buf *) b
              (*frame*) (pos - offset_L - offset_T) (pos - offset_L)
              (* new *) (B.loc_buffer_from_to
                         (* buf *) b
                         (*range*) (pos - offset_L) (pos))
              (* mem *) h0 h1;
    (* Prf *) assert (Seq.slice (B.as_seq h0 b) (v (pos - offset_L - offset_T)) (v (pos - offset_L))
                      `Seq.equal`
                      Seq.slice (B.as_seq h1 b) (v (pos - offset_L - offset_T)) (v (pos - offset_L)));
    // (* Prf *) writable_ext b (v (pos - offset_L - offset_T)) (v (pos - offset_L)) h0 h1;
    (* TODO: Should try `writable_replace_subseq`. *)
    (* NOTE: `writable` for some reason is not preserved by `serialize32`, maybe that's the hard part. *)
    (* Prf *) assume (writable b (v (pos - offset_L - offset_T)) (v (pos - offset_L)) h1); (* <-- FIXME *)
    let _ = serialize32_asn1_tag_backwards ()
            (* tag *) a
            (* buf *) b
            (* pos *) (pos - offset_L) in

    (* Prf *) let h2 = HST.get () in
    // (* Prf *) [@inline_let] let sx_L = serialize (serialize_bounded_der_length32 asn1_length_min asn1_length_max) len in
    // (* Prf *) [@inline_let] let sx_T = serialize (serialize_asn1_tag ()) a in
    // (* Prf *) [@inline_let] let sx_TL = serialize serialize_TL x in
    (* Prf *) assert (B.modifies (B.loc_buffer_from_to b (pos - offset_L) (pos)) h0 h1);
    (* Prf *) assert (B.modifies (B.loc_buffer_from_to b (pos - offset_L - offset_T) (pos - offset_L)) h1 h2);
    (* Prf *) assert (Seq.slice (B.as_seq h1 b) (v (pos - offset_L)) (v pos)
                      `Seq.equal`
                      serialize (serialize_bounded_der_length32 asn1_length_min asn1_length_max) len);
    (* NOTE: Need to prove the frame. *)
    (* Prf *) B.modifies_buffer_from_to_elim
              (* buf *) b
              (*frame*) (pos - offset_L) (pos)
              (* new *) (B.loc_buffer_from_to
                         (* buf *) b
                         (*range*) (pos - offset_L - offset_T) (pos - offset_L))
              (* mem *) h1 h2;
    (* Prf *) assert (Seq.slice (B.as_seq h1 b) (v (pos - offset_L)) (v pos)
                      `Seq.equal`
                      Seq.slice (B.as_seq h2 b) (v (pos - offset_L)) (v pos));
    (* Prf *) assert (Seq.slice (B.as_seq h2 b) (v (pos - offset_L)) (v pos)
                      `Seq.equal`     (* ^^^ FIXME *)
                      serialize (serialize_bounded_der_length32 asn1_length_min asn1_length_max) len);
    (* Prf *) assert (Seq.slice (B.as_seq h2 b) (v (pos - offset_L - offset_T)) (v (pos - offset_L))
                      `Seq.equal`
                      serialize (serialize_asn1_tag ()) a);
    (* Prf *) assert ((serialize (serialize_asn1_tag ()) a
                       `Seq.append`
                       serialize (serialize_bounded_der_length32 asn1_length_min asn1_length_max) len)
                       `Seq.equal`
                       serialize serialize_TL x);
    (* Prf *) assert (Seq.slice (B.as_seq h2 b) (v (pos - offset_L - offset_T)) (v pos)
                      `Seq.equal`
                      serialize serialize_TL x);

/// return offset
(*return*) (offset_L + offset_T)

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
