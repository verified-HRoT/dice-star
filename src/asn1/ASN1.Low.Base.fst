module ASN1.Low.Base

open ASN1.Base

include LowParse.Low.Base
include LowParse.Low.Combinators
// include LowParse.Bytes

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module MB = LowStar.Monotonic.Buffer
module B = LowStar.Buffer
module Cast = FStar.Int.Cast
open FStar.Integers

let size_t = U32.t
let byte_t = U8.t
let lbytes_t =  Seq.Properties.lseq byte_t

#push-options "--z3rlimit 32"
/// NOTE: Adapted from `LowParse.Low.Bytes.store_bytes
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
    v src_from <= v src_to /\ v src_to <= Seq.length src /\
    v dst_pos + (v src_to - v src_from) <= B.length dst /\
    writable dst (v dst_pos) (v dst_pos + (v src_to - v src_from)) h
  ))
  (ensures (fun h _ h' ->
    let s  = B.as_seq h  dst in
    let s' = B.as_seq h' dst in
    let pos = dst_pos in
    let offset = src_to - src_from in
    B.modifies (B.loc_buffer_from_to dst dst_pos (dst_pos + (src_to - src_from))) h h' /\
    writable dst (v dst_pos) (v dst_pos + (v src_to - v src_from)) h' /\
    Seq.slice s 0 (v pos) `Seq.equal` Seq.slice s' 0 (v pos) /\
    Seq.slice s (v (pos + offset)) (B.length dst) `Seq.equal` Seq.slice s' (v (pos + offset)) (B.length dst) /\
    Seq.slice (B.as_seq h' dst) (v dst_pos) (v dst_pos + (v src_to - v src_from))
    `Seq.equal`
    Seq.slice (src) (v src_from) (v src_to)
  ))
= (* Prf *) let h0 = HST.get () in
  let len = src_to - src_from in
  HST.push_frame ();
  (* Prf *) let h1 = HST.get () in
  let bi = B.alloca 0ul 1ul in
  (* Prf *) let h2 = HST.get () in
  C.Loops.do_while
    (fun h stop ->
      B.modifies (B.loc_union (B.loc_region_only true (HS.get_tip h1))
                              (B.loc_buffer_from_to dst dst_pos (dst_pos + len)))
                              h2 h /\
      B.live h bi /\
      writable dst (v dst_pos) (v dst_pos + (v src_to - v src_from)) h /\(
      let i = Seq.index (B.as_seq h bi) 0 in
      v i <= v len /\
      writable dst (v dst_pos) (v dst_pos + v len) h /\
      Seq.slice (B.as_seq h dst) (v dst_pos) (v dst_pos + v i)
      `Seq.equal`
      Seq.slice (src) (v src_from) (v src_from + v i) /\
      (stop == true ==> i == len)))
    (fun _ ->
      let i = B.index bi 0ul in
      if i = len then
      ( true )
      else
      ( let x = Seq.index src (v src_from + v i) in
        mbuffer_upd dst (v dst_pos) (v dst_pos + v len) (dst_pos + i) x
      ; let i' = i + 1ul in
        B.upd bi 0ul i'
      ; (* Prf *) let h' = HST.get () in
        (* Prf *) Seq.lemma_split (Seq.slice (B.as_seq h' dst) (v dst_pos) (v dst_pos + v i')) (v i)
      ; i' = len )
    );
  (* Prf *) HST.pop_frame ();
  let h3 = HST.get () in
  (* Prf *) B.modifies_buffer_from_to_elim
            (* buf *) dst
            (*frame*) 0ul dst_pos
            (* new *) (B.loc_buffer_from_to
                       (* buf *) dst
                       (*range*) dst_pos (dst_pos + len))
            (* mem *) h0 h3;
  (* Prf *) B.modifies_buffer_from_to_elim
            (* buf *) dst
            (*frame*) (dst_pos + len) (u (B.length dst))
            (* new *) (B.loc_buffer_from_to
                       (* buf *) dst
                       (*range*) dst_pos (dst_pos + len))
            (* mem *) h0 h3;
  (* Prf *) writable_modifies
            (* buf *) dst
            (* new *) (v dst_pos) (v (dst_pos + len))
            (* mem *) h0
            (* loc *) B.loc_none
            (* mem'*) h3

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
    let s  = B.as_seq h  b in
    let s' = B.as_seq h' b in
    Seq.length sx == v offset /\
    B.modifies (B.loc_buffer_from_to b (pos - offset) (pos)) h h' /\
    Seq.slice s 0 (v (pos - offset)) `Seq.equal` Seq.slice s' 0 (v (pos - offset)) /\
    Seq.slice s (v pos) (B.length b) `Seq.equal` Seq.slice s' (v pos) (B.length b) /\
    writable b (v (pos - offset)) (v pos) h' /\
    B.live h' b /\
    Seq.slice (B.as_seq h' b) (v pos - v offset) (v pos) `Seq.equal` sx)
