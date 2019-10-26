module RIoT.X509

open Common

open LowStar.BufferOps
open Lib.IntTypes

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
     data : B.lbuffer uint32 (v _BIGLEN)
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
     infinity: B.pointer uint32
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


let riot_kdf_fixed
  (fixed_size: I.uint_32{(v fixed_size) > 0})
  (fixed: B.lbuffer uint8 (v fixed_size))
  (label_size: I.uint_32)
  (label: B.lbuffer uint8 (v label_size))
  (context_size: I.uint_32)
  (context: B.lbuffer uint8 (v context_size))
  (numberOfBits: I.uint_32)
: HST.Stack unit
  (requires fun h ->
      B.live h fixed
    /\ B.live h label
    /\ B.live h context
    /\ B.disjoint fixed label
    /\ B.disjoint fixed context
    /\ B.disjoint context label)
  (ensures  fun h0 _ h1 -> True)
=
  HST.push_frame();

  let total_size: I.uint_32 =
      (if (!*fixed) = (u8 0x00) then fixed_size else 0ul)
    + (if (!*label) = (u8 0x00) then label_size else 0ul) in

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
