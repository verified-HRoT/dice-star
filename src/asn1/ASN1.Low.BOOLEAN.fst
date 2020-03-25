module ASN1.Low.BOOLEAN
///
/// ASN.1 Low
///
include LowParse.Low.Base
// include LowParse.Low.Combinators
include LowParse.Low.Int
// friend LowParse.Low.Int

include ASN1.Base
include ASN1.Spec.BOOLEAN
friend ASN1.Spec.BOOLEAN

open FStar.Integers
open Lib.IntTypes
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer

(* Boolean *)
inline_for_extraction
let make_constant_size_reader
  (sz: nat)
  (sz' : U32.t { U32.v sz' == sz } )
  (#t: Type0)
  (f: ((s: bytes {Seq.length s == sz}) -> GTot (option t)))
  (u: unit {
    make_constant_size_parser_precond sz t f
  })
  (f' : ((#rrel: _) -> (#rel: _) -> (s: B.mbuffer LowParse.Bytes.byte rrel rel) -> (pos: U32.t) -> HST.Stack (option t)
    (requires (fun h -> B.live h s /\ U32.v pos + sz <= B.length s))
    (ensures (fun h res h' ->
      B.modifies B.loc_none h h' /\
      res == f (Seq.slice (B.as_seq h s) (U32.v pos) (U32.v pos + sz))
  ))))
: Tot (leaf_reader (make_constant_size_parser sz t f))
= fun #rrel #rel sl pos ->
  let h = HST.get () in
  [@inline_let] let _ = valid_facts (make_constant_size_parser sz t f) h sl pos in
  Some?.v (f' sl.base pos)

inline_for_extraction
let read_asn1_boolean ()
: Tot (leaf_reader (parse_asn1_boolean))
= decode_asn1_boolean_injective ();
  make_constant_size_reader 1 1ul
    decode_asn1_boolean ()
    (fun #rrel #rel input pos ->
      let r = B.index input pos in
      decode_asn1_boolean (Seq.create 1 r))

open LowParse.Bytes

// [.........[TAG] [LENGTH] [VALUE]]

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
  (pos: U32.t) ->
  HST.Stack (len: U32.t)
  (requires (fun h ->
    let len = Seq.length (serialize s x) in
    let sq = B.as_seq h b in
    B.live h b /\
    (* NOTE: Have enough space *)
    len <= U32.v pos /\ U32.v pos <= B.length b /\
    writable b (U32.v pos - len) (U32.v pos) h
  ))
  (ensures (fun h len h' ->
    Seq.length (serialize s x) == U32.v len /\ (
    B.modifies (B.loc_buffer_from_to b (pos `U32.sub` len) pos) h h' /\
    B.live h b /\
    (U32.v pos - U32.v len) <= (U32.v pos) /\
    (U32.v pos) <= Seq.length (B.as_seq h' b) /\
    Seq.slice (B.as_seq h' b) (U32.v pos - U32.v len) (U32.v pos) `Seq.equal` serialize s x
  )))

inline_for_extraction
let serialize32_backwards_asn1_boolean ()
: Tot (serializer32_backwards serialize_asn1_boolean)
= fun (x: bool) #rrel #rel b pos ->
  let content = encode_asn1_boolean x in
  mbuffer_upd b (Ghost.hide (v pos - 1)) (Ghost.hide (v pos)) (pos `U32.sub` 1ul) content;
  1ul

(* NOTE: NEW strong prefix lear_writer type with offset, meant to
         support backward serialization, needs the ad-hoc `slice`
         with `offset`. *)
[@unifier_hint_injective]
inline_for_extraction
let leaf_writer_offset_strong
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
: Tot Type
= (x: t) ->
  (#rrel: _) -> (#rel: _) ->
  (sl: slice rrel rel) ->
  (pos: U32.t) ->
  HST.Stack U32.t
  (requires (fun h ->
    let sq = B.as_seq h sl.base in
    let len = serialized_length s x in
    live_slice h sl /\
    U32.v pos + len <= U32.v sl.len /\
    writable sl.base (U32.v pos) (U32.v pos + len) h
  ))
  (ensures (fun h pos' h' ->
    B.modifies (loc_slice_from_to sl pos pos') h h' /\
    valid_content_pos p h' sl pos x pos'
  ))


inline_for_extraction
let leaf_writer_offest_strong_of_serializer32
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p)
  (s32: serializer32 s)
  (u: squash (k.parser_kind_subkind == Some ParserStrong))
: Tot (leaf_writer_strong s)
= fun x #rrel #rel input pos ->
  let h0 = HST.get () in
  let len = s32 x input.base pos in
  [@inline_let]
  let pos' = pos `U32.add` len in
  let h = HST.get () in
  [@inline_let] let _ =
    let large = bytes_of_slice_from h input pos in
    let small = bytes_of_slice_from_to h input pos pos' in
    parse_strong_prefix p small large;
    valid_facts p h input pos
  in
  pos'


inline_for_extraction
let write_asn1_boolean ()
: leaf_writer_strong (serialize_asn1_boolean)
= leaf_writer_strong_of_serializer32 (serialize32_asn1_boolean ()) ()

inline_for_extraction
let jump_asn1_boolean ()
: jumper parse_asn1_boolean
= jump_constant_size (parse_asn1_boolean) 1ul ()

let valid_asn1_boolean
  (h: HS.mem)
  (#rrel #rel: _)
  (input: slice rrel rel)
  (pos: pub_uint32)
: Lemma (
  valid parse_asn1_boolean h input pos
  <==>
 (valid parse_u8 h input pos /\
  Some? (decode_asn1_boolean (Seq.create 1 (contents parse_u8 h input pos)))))
= valid_facts parse_asn1_boolean h input pos;
  valid_facts parse_u8           h input pos;
  parse_asn1_boolean_unfold (bytes_of_slice_from h input pos)

inline_for_extraction
let validate_asn1_boolean ()
: Tot (validator parse_asn1_boolean)
= fun #rrel #rel (input: slice rrel rel) (pos: pub_uint32) ->
  let h = HST.get () in
  valid_asn1_boolean   h input pos;
  valid_equiv parse_u8 h input pos;
  if (input.len - pos) < 1ul then
  ( validator_error_not_enough_data )
  else
  ( let b = read_u8 input pos  in
    let x = decode_asn1_boolean (Seq.create 1 b) in
    if Some? x then
    ( pos + 1ul )
    else
    ( validator_error_generic ))
