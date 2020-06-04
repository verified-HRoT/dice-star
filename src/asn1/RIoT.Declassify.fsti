module RIoT.Declassify

open Lib.IntTypes

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer
module C = C
module B32 = FStar.Bytes

noextract
val declassify_secret_bytes
  (l: nat)
  (sec: Seq.lseq uint8 l)
: GTot (pub: Seq.lseq pub_uint8 l
          { forall (i:nat{i < l}).
              v (Seq.index sec i) == v (Seq.index pub i) })

noextract
val classify_public_bytes
  (l: nat)
  (pub: Seq.lseq pub_uint8 l)
: GTot (sec: Seq.lseq uint8 l
          { forall (i:nat{i < l}).
              v (Seq.index sec i) == v (Seq.index pub i) })

val declassify_secret_buffer
  (len: size_t)
  (src: B.lbuffer uint8 (v len))
  (dst: B.lbuffer pub_uint8 (v len))
: HST.Stack unit
  (requires fun h ->
    B.live h src /\ B.live h src /\
    B.disjoint src dst)
  (ensures fun h0 _ h1 ->
    B.(modifies (loc_buffer dst) h0 h1) /\
    B.as_seq h1 dst == declassify_secret_bytes (v len) (B.as_seq h1 src))

val classify_public_buffer
  (len: size_t)
  (src: B.lbuffer pub_uint8 (v len))
  (dst: B.lbuffer uint8 (v len))
: HST.Stack unit
  (requires fun h ->
    B.live h src /\ B.live h src /\
    B.disjoint src dst)
  (ensures fun h0 _ h1 ->
    B.(modifies (loc_buffer dst) h0 h1) /\
    B.as_seq h1 dst == classify_public_bytes (v len) (B.as_seq h1 src))
