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
module G = FStar.Ghost
module IB = LowStar.ImmutableBuffer
module B32 = FStar.Bytes
open FStar.Integers

let size_t = U32.t
let byte = uint_8

// AR: are the following used?
// let bytes = Seq.seq byte
// let lbytes = Seq.Properties.lseq byte

(* NOTE: Let's see if this works *)
// #push-options "--fuel 1"
// noextract inline_for_extraction
// let igcmalloc_s32_of_list
//   (r:HS.rid)
//   (len: size_t)
//   (init:list byte { List.length init == v len })
// : HST.ST (s32: B32.bytes
//                { B32.length s32 == v len /\
//                  s32 == B32.hide (Seq.createL init) })
//   (requires fun h -> True)
//   (ensures fun h0 s32 h1 -> B.(modifies loc_none h0 h1))
// = let ib = IB.igcmalloc_of_list HS.root init in
//   B32.of_buffer len ib
// #pop-options

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
  (b: B.mbuffer byte rrel rel) ->
  (pos: UInt32.t) ->
  HST.Stack UInt32.t
  (* NOTE: b[pos] is already written, and b[pos - offset, pos - 1] will be written. *)
  (requires fun h ->
    let offset = Seq.length (s `serialize` x) in
    B.live h b /\
    offset <= UInt32.v pos /\ UInt32.v pos <= B.length b /\
    writable b (UInt32.v pos - offset) (UInt32.v pos) h)
  (ensures fun h offset h' ->
    Seq.length (s `serialize` x) == v offset /\
    B.modifies (B.loc_buffer_from_to b (UInt32.sub pos offset) (pos)) h h' /\
    B.live h' b /\
    Seq.slice (B.as_seq h' b) (UInt32.v (UInt32.sub pos offset)) (v pos) `Seq.equal` (s `serialize` x))

unfold
let coerce_serializer32_backwards
  (#t2: Type0)
  (#k: parser_kind)
  (#t1: Type0)
  (#p1: parser k t1)
  (#p2: parser k t2)
  (#s1: serializer p1)
  (s2: serializer p2)
  (s32: serializer32_backwards s1)
  (u: unit { t2 == t1 /\ p2 == coerce_parser t2 p1 /\ s2 == ASN1.Spec.Base.coerce_parser_serializer p2 s1 ()} )
: Tot (serializer32_backwards (s2))
= s32

inline_for_extraction
let frame_serializer32_backwards
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p)
  (s32: serializer32_backwards s)
  (x: t)
  (#rrel: _)
  (#rel: _)
  (b: B.mbuffer byte rrel rel)
  (posl: Ghost.erased size_t)
  (posr: Ghost.erased size_t)
  (pos: size_t)
: HST.Stack U32.t
  (requires (fun h ->
    let offset = Seq.length (serialize s x) in
    let sq = B.as_seq h b in
    B.live h b /\
    v posl + offset <= v pos /\ v pos <= v posr /\ v posr <= B.length b /\
    writable b (v posl) (v posr) h
  ))
  (ensures (fun h offset h' ->
    let sx = serialize s x in
    let s  = B.as_seq h  b in
    let s' = B.as_seq h' b in
    Seq.length sx == v offset /\ (
    B.modifies (B.loc_buffer_from_to b posl posr) h h' /\
    B.live h' b /\
    Seq.slice s (v posl) (v (pos - offset)) `Seq.equal` Seq.slice s' (v posl) (v (pos - offset)) /\
    Seq.slice s (v pos) (v posr) `Seq.equal` Seq.slice s' (v pos) (v posr) /\
    writable b (v posl) (v posr) h' /\
    Seq.slice s' (v (pos - offset)) (v pos) `Seq.equal` sx
  )))
=
  (* Prf *) let h0 = HST.get () in

  (* NOTE: Prove writability of the to-be-written range of b[posl, posr]. *)
  (* Prf *) writable_weaken b
            (*range*) (v posl) (v posr)
            (* mem *) h0
            (* dst *) (v pos - Seq.length (serialize s x)) (v pos);

  (* NOTE: Serialization. *)
  let offset = s32 x b pos in

  (* Prf *) let h1 = HST.get () in

  (* NOTE: Retain writability of b[posl, posr]. *)
  (* Prf *) B.loc_includes_loc_buffer_from_to b
            (*range*) posl posr
            (* new *) (pos - offset) pos;
  (* Prf *) writable_modifies b
            (*range*) (v posl) (v posr)
            (*from *) h0
            (*other*) B.loc_none
            (*to   *) h1;

  (* NOTE: Prove b[posl, pos - offset] is not modified from `h0` to `h1`. *)
  (* Prf *) B.loc_includes_loc_buffer_from_to b
            (*range*) posl posr
            (*frame*) posl (pos - offset);
  (* Prf *) B.loc_disjoint_loc_buffer_from_to b
            (*frame*) posl (pos - offset)
            (* new *) (pos - offset) pos;
  (* Prf *) B.modifies_buffer_from_to_elim b
            (*frame*) posl (pos - offset)
            (* new *) (B.loc_buffer_from_to b (pos - offset) pos)
            (* mem *) h0 h1;

  (* NOTE: Prove b[pos, posr] is s not modified from `h0` to `h1`. *)
  (* Prf *) B.loc_includes_loc_buffer_from_to b
            (*range*) posl posr
            (*frame*) pos posr;
  (* Prf *) B.loc_disjoint_loc_buffer_from_to b
            (* new *) (pos - offset) pos
            (*frame*) pos posr;
  (* Prf *) B.modifies_buffer_from_to_elim b
            (*frame*) pos posr
            (* new *) (B.loc_buffer_from_to b (pos - offset) pos)
            (* mem *) h0 h1;

(* return *) offset

/// Backwards combinators
///
inline_for_extraction
let serialize32_nondep_then_backwards
  (#k1: parser_kind)
  (#t1: Type0)
  (#p1: parser k1 t1)
  (#s1: serializer p1)
  (ls1 : serializer32_backwards s1 { k1.parser_kind_subkind == Some ParserStrong })
  (#k2: parser_kind)
  (#t2: Type0)
  (#p2: parser k2 t2)
  (#s2: serializer p2)
  (ls2 : serializer32_backwards s2)
: Tot (serializer32_backwards (s1 `serialize_nondep_then` s2))
= fun x #rrel #rel b pos ->
  match x with
  | Mktuple2 x1 x2 ->
    (* Prf *) serialize_nondep_then_eq s1 s2 x;
    (* Prf *) let posl = Ghost.hide (pos - u (Seq.length (serialize (s1   `serialize_nondep_then` s2) x))) in
    (* Prf *) let posr = Ghost.hide pos in

    let offset2 = frame_serializer32_backwards ls2 x2 b posl posr pos in

    let pos = pos - offset2 in
    let offset1 = frame_serializer32_backwards ls1 x1 b posl posr pos in

  (* return *) offset1 + offset2

inline_for_extraction
let serialize32_tagged_union_backwards
  (#kt: parser_kind{kt.parser_kind_subkind == Some ParserStrong})
  (#tag_t: Type0)
  (#pt: parser kt tag_t)
  (#st: serializer pt)
  (lst: serializer32_backwards st)
  (#data_t: Type0)
  (#tag_of_data: (data_t -> GTot tag_t))
  (tag_of_data_impl: (d: data_t -> Tot (tg: tag_t{tg == tag_of_data d})))
  (#k: parser_kind)
  (#p: (t: tag_t) -> Tot (parser k (refine_with_tag tag_of_data t)))
  (#s: (t: tag_t) -> Tot (serializer (p t)))
  (ls: (t: tag_t) -> Tot (serializer32_backwards (s t)))
: Tot (serializer32_backwards (serialize_tagged_union st tag_of_data s))
= fun (x: data_t) #rrel #rel b pos ->
  [@inline_let]
  let tg = tag_of_data_impl x in
  (* Prf *) serialize_tagged_union_eq
            (* st *) (st)
            (* tg *) (tag_of_data)
            (* s  *) (s)
            (* in *) (x);

  (* Prf *) let posl = Ghost.hide (pos - u (Seq.length (serialize (serialize_tagged_union st tag_of_data s) x))) in
  (* Prf *) let posr = Ghost.hide pos in

  let offset_data = frame_serializer32_backwards (ls tg) x b posl posr pos in

  let pos = pos - offset_data in
  let offset_tag = frame_serializer32_backwards lst tg b posl posr pos in

(* return *) offset_tag + offset_data

inline_for_extraction
let serialize32_weaken_backwards
  (#k: parser_kind)
  (#t: Type0)
  (k' : parser_kind)
  (#p: parser k t)
  (#s: serializer p { k' `is_weaker_than` k })
  (ls: serializer32_backwards s)
: Tot (ls': serializer32_backwards (k' `serialize_weaken` s))
= fun (x:t) #rrel #rel b pos
-> ls x b pos

inline_for_extraction
let serialize32_filter_backwards
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p)
  (s32: serializer32_backwards s)
  (f: (t -> GTot bool))
: Tot (serializer32_backwards (serialize_filter s f))
= fun x #rrel #rel input pos ->
  s32 x input pos

inline_for_extraction
let serialize32_synth_backwards
  (#k: parser_kind)
  (#t1: Type)
  (#p1: parser k t1)
  (#s1: serializer p1)
  (s1' : serializer32_backwards s1)
  (#t2: Type)
  (f2: t1 -> GTot t2)
  (g1: t2 -> GTot t1)
  (g1' : (x2: t2) -> Tot (x1: t1 { x1 == g1 x2 } ))
  (u: squash (synth_injective f2 /\ synth_inverse f2 g1))
: Tot (serializer32_backwards (serialize_synth p1 f2 s1 g1 u))
= fun x #rrel #rel input pos ->
  [@inline_let] let _ =
    serialize_synth_eq p1 f2 s1 g1 () x
  in
  s1' (g1' x) input pos


inline_for_extraction noextract
let msnd (#a:Type) (#b:Type) (x:a & b) : b = match x with
  | Mktuple2 _ x -> x

