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
open Lib.IntTypes

#push-options "--z3rlimit 32"

/// NOTE: Adapted from `LowParse.Low.Bytes.store_bytes`
inline_for_extraction
let store_bytes
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
  (requires fun h ->
    let len = Seq.length (serialize s x) in
    B.live h b /\
    len <= v pos /\ v pos <= B.length b /\
    writable b (v pos - len) (v pos) h)
  (ensures fun h offset h' ->
    let sx = serialize s x in
    Seq.length sx == v offset /\
    B.modifies (B.loc_buffer_from_to b (pos -! offset) pos) h h' /\
    B.live h b /\
    Seq.slice (B.as_seq h' b) (v pos - v offset) (v pos) `Seq.equal` sx)

/// NOTE: Inlining all low-level serializers for now
inline_for_extraction
let serialize32_asn1_value_backwards_attempt
  (x: valid_asn1_TL) (* FIXME: I doubt if we could know this ahead. *)
: serializer32_backwards (serialize_asn1_value x)
= fun (value: asn1_value_of_TL x)
    (#rrel #rel: _)
    (b: B.mbuffer byte_t rrel rel)
    (pos: size_t)
->  let a, offset = x in
    (* Prf *) serialize_asn1_value_unfold x value;
    (* Prf *) assert (v offset == Seq.length (serialize (serialize_asn1_value x) value));
    [@inline_let] let gstart = Ghost.hide (v pos - v offset) in
    [@inline_let] let gend   = Ghost.hide (v pos) in
    [@inline_let] let i      = pos -! offset in
    (* Prf *) assert (Ghost.reveal gstart <= v i);
    match a with
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
                      ; (* return *) offset )

/// NOTE: Backward version of `LowParse.Low.DER.serialize32_bounded_der_length32`
let serialize32_bounded_der_length32_backwards
  (min: der_length_t)
  (max: der_length_t { min <= max /\ max < 4294967296 } )
: Tot (serializer32_backwards (serialize_bounded_der_length32 min max))
= fun (y' : bounded_int32 (min) (max))
    (#rrel #rel: _)
    (b: B.mbuffer byte_t rrel rel)
    (pos: size_t)
->  admit();
    [@inline_let]
    let gpos  = Ghost.hide (v pos - Seq.length (serialize (serialize_bounded_der_length32 min max) y')) in
    [@inline_let]
    let gpos' = Ghost.hide (v pos) in
    [@inline_let]
    let _ =
      serialize_bounded_der_length32_unfold (min) (max) y'
    in
    let x = tag_of_der_length32_impl y' in
    if x `U8.lt` 128uy
    then begin
      mbuffer_upd b gpos gpos' pos x;
      1ul
    end else
    if x = 129uy
    then begin
      mbuffer_upd b gpos gpos' (pos -! 1ul) x;
      mbuffer_upd b gpos gpos' pos (Cast.uint32_to_uint8 y');
      2ul
    end else
    if x = 130uy
    then begin
      admit();
      mbuffer_upd b gpos gpos' (pos -! 2ul) x;
      let h = HST.get () in
      writable_weaken  b (Ghost.reveal gpos) (Ghost.reveal gpos') h (U32.v pos + 1) (U32.v pos + 3);
      let z = serialize32_bounded_integer_2 () y' b (pos `U32.add` 1ul) in
      let h' = HST.get () in
      Seq.lemma_split (Seq.slice (B.as_seq h' b) (U32.v pos) (U32.v pos + 3)) 1;
      B.modifies_buffer_from_to_elim b pos (pos `U32.add` 1ul) (B.loc_buffer_from_to b (pos `U32.add` 1ul) (pos `U32.add` 3ul)) h h' ;
      3ul // 1ul `U32.add` z
    end else
  if x = 131uy
  then begin
    admit();
    mbuffer_upd b gpos gpos' pos x;
    let h = HST.get () in
    writable_weaken b (Ghost.reveal gpos) (Ghost.reveal gpos') h (U32.v pos + 1) (U32.v pos + 4);
    let z = serialize32_bounded_integer_3 () y' b (pos `U32.add` 1ul) in
    let h' = HST.get () in
    Seq.lemma_split (Seq.slice (B.as_seq h' b) (U32.v pos) (U32.v pos + 4)) 1;
    B.modifies_buffer_from_to_elim b pos (pos `U32.add` 1ul) (B.loc_buffer_from_to b (pos `U32.add` 1ul) (pos `U32.add` 4ul)) h h' ;
    4ul // 1ul `U32.add` z
  end else begin
    admit();
    mbuffer_upd b gpos gpos' pos x;
    let h = HST.get () in
    writable_weaken b (Ghost.reveal gpos) (Ghost.reveal gpos') h (U32.v pos + 1) (U32.v pos + 5);
    let z = serialize32_bounded_integer_4 () y' b (pos `U32.add` 1ul) in
    let h' = HST.get () in
    Seq.lemma_split (Seq.slice (B.as_seq h' b) (U32.v pos) (U32.v pos + 5)) 1;
    B.modifies_buffer_from_to_elim b pos (pos `U32.add` 1ul) (B.loc_buffer_from_to b (pos `U32.add` 1ul) (pos `U32.add` 5ul)) h h' ;
    5ul // 1ul `U32.add` z
  end

/// TODO: Easy.
let serialize32_asn1_tag_backwards ()
: Tot (serializer32_backwards (serialize_asn1_tag ()))
= admit()


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
