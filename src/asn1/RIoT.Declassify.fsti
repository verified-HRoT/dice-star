module RIoT.Declassify

open Lib.IntTypes

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer
module C = C
module B32 = FStar.Bytes

val riot_declassify_public_key
  (src: B.lbuffer uint8 32)
  (dst: B.lbuffer pub_uint8 32)
: HST.Stack unit
  (requires fun h ->
    B.live h src /\ B.live h src /\
    B.disjoint src dst)
  (ensures fun h0 _ h1 ->
    B.(modifies (loc_buffer dst) h0 h1) /\
   (let src_seq = B.as_seq h1 src in
    let dst_seq = B.as_seq h1 dst in
    forall (i:nat{0 <= i /\ i < 32}).
      v (Seq.index dst_seq i) == v (Seq.index src_seq i)))

val riot_declassify_signature
  (src: B.lbuffer uint8 64)
  (dst: B.lbuffer pub_uint8 64)
: HST.Stack unit
  (requires fun h ->
    B.live h src /\ B.live h src /\
    B.disjoint src dst)
  (ensures fun h0 _ h1 ->
    B.(modifies (loc_buffer dst) h0 h1) /\
   (let src_seq = B.as_seq h1 src in
    let dst_seq = B.as_seq h1 dst in
    forall (i:nat{0 <= i /\ i < 64}).
      v (Seq.index dst_seq i) == v (Seq.index src_seq i)))
