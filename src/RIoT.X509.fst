module RIoT.X509

open Common

open LowStar.BufferOps
open FStar.Integers
//open Lib.IntTypes

open Spec.Hash.Definitions
open Hacl.Hash.Definitions

module I  = FStar.Integers
module HI  = Lib.IntTypes

module SHA2= Hacl.Hash.SHA2
module HMAC= Hacl.HMAC
module Ed25519 = Hacl.Ed25519

module CL  = C.Loops
module CE  = C.Endianness
module CF  = C.Failure
module C   = C
module CS  = C.String
module S   = FStar.Seq
module IB  = LowStar.ImmutableBuffer
module B   = LowStar.Buffer
module M   = LowStar.Modifies
module HS  = FStar.HyperStack
module HST = FStar.HyperStack.ST

let _BIGLEN : I.uint_32 = 0x09ul

noeq
type bigval_t = {
     data : B.lbuffer HI.uint32 (v _BIGLEN)
  }

/// REF:
/// typedef struct {
///     bigval_t x;
///     bigval_t y;
///     uint32_t infinity;
/// } affine_point_t;
noeq
type affine_point_t = {
     x: bigval_t;
     y: bigval_t;
     infinity: B.pointer HI.uint32
  }
type riot_ecc_publickey = affine_point_t


let live_affine_point
  (h: HS.mem)
  (p: affine_point_t)
: Type0
=   B.live h p.x.data
  /\ B.live h p.y.data
  /\ B.live h p.infinity
let live_ecc_publickey = live_affine_point

/// REF:
/// typedef struct {
///     bigval_t r;
///     bigval_t s;
/// } ECDSA_sig_t;
noeq
type ecdsa_sig_t = {
     r: bigval_t;
     s: bigval_t
  }
type riot_ecc_privatekey = ecdsa_sig_t

let live_ecdsa_sig
  (h: HS.mem)
  (s: ecdsa_sig_t)
: Type0
=   B.live h s.r.data
  /\ B.live h s.s.data
type live_ecc_privatekey = live_ecdsa_sig

#set-options "--max_fuel 50 --max_ifuel 50"
#push-options "--query_stats"
(*)
val memcpy: #a:eqtype -> src:B.buffer a -> dst:B.buffer a -> len:I.uint_32 -> HST.Stack unit
  (requires fun h0 ->
    let l_src = M.loc_buffer src in
    let l_dst = M.loc_buffer dst in
    B.live h0 src /\ B.live h0 dst /\
    B.length src = I.v len /\
    B.length dst = I.v len /\
    M.loc_disjoint l_src l_dst)
  (ensures fun h0 () h1 ->
    let l_src = M.loc_buffer src in
    let l_dst = M.loc_buffer dst in
    B.live h1 src /\
    B.live h1 dst /\
    M.(modifies l_dst h0 h1) /\
    S.equal (B.as_seq h1 dst) (B.as_seq h0 src))
let memcpy #a src dst len =
  let h0 = HST.get () in
  let inv h (i: nat) =
    B.live h src /\ B.live h dst /\
    M.(M.modifies (M.loc_buffer dst) h0 h) /\
    i <= I.v len /\
    S.equal (Seq.slice (B.as_seq h src) 0 i) (Seq.slice (B.as_seq h dst) 0 i)
  in
  let body (i: I.uint_32{ 0 <= I.v i /\ I.v i < I.v len }): HST.Stack unit
    (requires (fun h -> inv h (I.v i)))
    (ensures (fun h0 () h1 -> inv h0 (I.v i) /\ inv h1 (I.v i + 1)))
  =
    let open B in
    dst.(i) <- src.(i)
  in
  C.Loops.for 0ul len inv body
*)
let rec memcpy
  (#a:eqtype)
  (dst: B.buffer a)
  (src: B.buffer a)
  (len: I.uint_32)
: HST.Stack unit
  (requires fun h ->
      B.live h dst
    /\ B.live h src
    /\ B.disjoint dst src
    /\ len > 0ul
    /\ len <= B.len src
    /\ B.len src <= B.len dst)
  (ensures  fun h0 _ h1 ->
      M.modifies (M.loc_buffer dst) h0 h1
/// TODO: /\ (S.slice (B.as_seq h1 dst) 0 (v len - 1)) `S.equal` (S.slice (B.as_seq h1 src) 0 (v len - 1))
    )
=
  let cur = len - 1ul in
  dst.(cur) <- src.(cur);
  match cur with
  | 0ul -> ()
  | _   -> memcpy dst src cur

#reset-options "--z3rlimit 50 --max_fuel 50 --max_ifuel 50"
let riot_kdf_fixed
  (#fixed_size: I.uint_32{(v fixed_size) > 0})
  (fixed: B.lbuffer HI.uint8 (v fixed_size))
  (#label_size: I.uint_32{(v label_size) > 0})
  (label: B.lbuffer HI.uint8 (v label_size))
  (#context_size: I.uint_32{(v context_size) > 0})
  (context: B.lbuffer HI.uint8 (v context_size))
  (numberOfBits: I.uint_32)
  (total_size: B.pointer I.uint_32)
: HST.Stack unit
  (requires fun h ->
      B.live h fixed
    /\ B.live h label
    /\ B.live h context
    /\ B.live h total_size
    /\ B.disjoint fixed label
    /\ B.disjoint fixed context
    /\ B.disjoint context label
    /\ B.disjoint total_size fixed
    /\ B.disjoint total_size label
    /\ B.disjoint total_size context
    /\ I.ok (+) label_size context_size
    /\ I.ok (+) (label_size + context_size) 5ul
/// REF: assert(fixedSize >= total);
    /\ fixed_size >= (label_size + context_size + 5ul))
  (ensures  fun h0 _ h1 -> True)
=
  HST.push_frame();

/// REF: size_t  total = (((label) ? labelSize : 0) + ((context) ? contextSize : 0) + 5);
  total_size.(0ul) <- label_size + context_size + 5ul;

/// REF: if (label) {
///        memcpy(fixed, label, labelSize);
///        fixed += labelSize;
///    }
  //memcpy fixed label label_size;
  let fixed' = B.sub fixed 0ul label_size in

/// REF: *fixed++ = 0;
  fixed'.(1ul) <- (HI.u8 0x00);

/// REF: if (context) {
///        memcpy(fixed, context, contextSize);
///        fixed += contextSize;
///      }
  //memcpy fixed' context context_size;
  let fixed'' = B.sub fixed 0ul label_size in

/// REF: numberOfBits = UINT32_TO_BIGENDIAN(numberOfBits);

/// REF: memcpy(fixed, &numberOfBits, 4);
  //memcpy fixed''
/// REF: return total;

  HST.pop_frame()

let ecdh_derive
  (p1: affine_point_t)
  (k: bigval_t)
  (src: bigval_t)
  (label_size: I.uint_32)
  (label: B.lbuffer uint8 (I.v label_size))
: HST.Stack unit
  (requires fun h ->
      live_affine_point h p1
    /\ B.live h k.data)
  (ensures  fun h0 _ h1 -> True)
=
  HST.push_frame();

  k.data.(1ul) <- (u32 0);

  HST.pop_frame()
