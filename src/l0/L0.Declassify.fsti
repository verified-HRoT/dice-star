module L0.Declassify

open Lib.IntTypes

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer
module C = C
module B32 = FStar.Bytes

noextract
val declassify_secret_bytes
  (sec: Seq.seq uint8)
: GTot (pub: Seq.seq pub_uint8
          { Seq.length sec == Seq.length pub /\
            (forall (i:nat{i < Seq.length pub}).
              v (Seq.index sec i) == v (Seq.index pub i)) })

noextract
val classify_public_bytes
  (pub: Seq.seq pub_uint8)
: GTot (sec: Seq.seq uint8
          { Seq.length sec == Seq.length pub /\
            (forall (i:nat{i < Seq.length pub}).
              v (Seq.index sec i) == v (Seq.index pub i)) })

val declassify_secret_buffer
  (len: UInt32.t)
  (src: B.lbuffer uint8 (UInt32.v len))
  (dst: B.lbuffer pub_uint8 (UInt32.v len))
: HST.Stack unit
  (requires fun h ->
    B.live h src /\ B.live h dst /\
    B.disjoint src dst)
  (ensures fun h0 _ h1 ->
    B.live h1 src /\ B.live h1 dst /\
    B.(modifies (loc_buffer dst) h0 h1) /\
    B.as_seq h1 dst == declassify_secret_bytes (B.as_seq h1 src))

val classify_public_buffer
  (len: size_t)
  (src: B.lbuffer pub_uint8 (v len))
  (dst: B.lbuffer uint8 (v len))
: HST.Stack unit
  (requires fun h ->
    B.live h src /\ B.live h dst /\
    B.disjoint src dst)
  (ensures fun h0 _ h1 ->
    B.live h1 src /\ B.live h1 dst /\
    B.(modifies (loc_buffer dst) h0 h1) /\
    B.as_seq h1 dst == classify_public_bytes (B.as_seq h1 src))
