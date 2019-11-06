/// Reference: https://github.com/microsoft/RIoT/blob/master/Reference/DICE/DiceCore.cpp
module DICE.Core


open LowStar.BufferOps
open Lib.IntTypes
open FStar.Integers

open Spec.Hash.Definitions
open Hacl.Hash.Definitions

module I  = FStar.Integers
module HI  = Lib.IntTypes

module SHA2= Hacl.Hash.SHA2
// module HMAC= Hacl.HMAC
// module Ed25519 = Hacl.Ed25519

// module CL  = C.Loops
// module CE  = C.Endianness
// module CF  = C.Failure
// module C   = C
// module CS  = C.String
// module S   = FStar.Seq
// module IB  = LowStar.ImmutableBuffer
module B   = LowStar.Buffer
module M   = LowStar.Modifies
module HS  = FStar.HyperStack
module HST = FStar.HyperStack.ST



/// UDS type
type uds_t (size: nat) = B.lbuffer HI.uint8 size

/// CDI type, an alias of the hash digest type in Hacl*.
type cdi_t (alg: hash_alg) = hash_t alg


/// <><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>

/// An API to get UDS.
/// REF: None
assume val get_UDS
  (size: nat)
: HST.Stack (b:B.buffer HI.uint8 {B.length b = size})
  (requires fun _ -> True)
  (ensures  fun h0 uds h1 ->
      B.live h1 uds)

assume val get_Measurement
  (alg: hash_alg)
: HST.Stack (hash_t alg)
  (requires fun _ -> True)
  (ensures  fun h0 r h1 ->
      B.live h1 r)

/// REF: void DiceSHA256 (
///        const uint8_t *buf,
///        size_t bufSize,
///        uint8_t *digest
///      )
assume val diceSHA256
  (size : nat)
  (data: B.lbuffer HI.uint8 size)
  (digest: hash_t SHA2_256)
: HST.Stack unit
  (requires fun h ->
      B.live h data
    /\ B.live h digest
    /\ B.disjoint data digest)
  (ensures  fun h0 _ h1 ->
      B.modifies (B.loc_buffer digest) h0 h1)
///      {
///          DICE_SHA256_CONTEXT context;
///          DICE_SHA256_Init(&context);
///          DICE_SHA256_Update(&context, buf, bufSize);
///          DICE_SHA256_Final(&context, digest);
///      }


/// REF: void DiceSHA256_2 (
///        const uint8_t *buf1,
///        size_t bufSize1,
///        const uint8_t *buf2,
///        size_t bufSize2,
///        uint8_t *digest
///      )
assume val diceSHA256_2
  (size1 : nat)
  (data1: B.lbuffer HI.uint8 size1)
  (size2 : nat)
  (data2 : B.lbuffer HI.uint8 size2)
  (digest: hash_t SHA2_256)
: HST.Stack unit
  (requires fun h ->
      B.live h data1
    /\ B.live h data2
    /\ B.live h digest
    /\ B.disjoint data1 data2
    /\ B.disjoint data1 digest
    /\ B.disjoint data2 digest)
  (ensures  fun h0 _ h1 ->
      B.modifies (B.loc_buffer digest) h0 h1)
///      {
///          DICE_SHA256_CONTEXT context;
///          DICE_SHA256_Init(&context);
///          DICE_SHA256_Update(&context, buf1, bufSize1);
///          DICE_SHA256_Update(&context, buf2, bufSize2);
///          DICE_SHA256_Final(&context, digest);
///      }


/// <><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>


/// DICE definitions
/// REF: #define DICE_UDS_LENGTH         0x20
///      #define DICE_DIGEST_LENGTH      0x20
let _DICE_UDS_LENGTH    = 0x20
let _DICE_DIGEST_LENGTH: uint_32 = hash_len SHA2_256


/// <><><><><><><><><><><><><><><><><> DICE Core main funtion <><><><><><><><><><><><><><><><><><><


#reset-options "--z3rlimit 50"
let main ()
: HST.Stack C.exit_code
  (requires fun h -> True)
  (ensures  fun _ _ _ -> True)
=
  HST.push_frame();

/// NOTE: compute digest `uDigest` of `uds`
  let uds : uds_t _DICE_UDS_LENGTH = get_UDS _DICE_UDS_LENGTH in
  let uDigest :hash_t SHA2_256 = B.alloca (HI.u8 0x00) (hash_len SHA2_256) in
    SHA2.hash_256
      uds
      (u _DICE_UDS_LENGTH)
      uDigest;

/// NOTE: compute digest `rDigest` of `measurement`
  let measurement: hash_t SHA2_256 = get_Measurement SHA2_256 in
  let rDigest :hash_t SHA2_256 = B.alloca (HI.u8 0x00) (hash_len SHA2_256) in
    SHA2.hash_256
      measurement
      (hash_len SHA2_256)
      rDigest;

    let cdi: cdi_t SHA2_256
      = B.alloca (HI.u8 0x00) (hash_len SHA2_256) in

    diceSHA256_2
     (v (hash_len SHA2_256)) uDigest
     (v (hash_len SHA2_256)) rDigest
     cdi;

    B.fill uDigest (HI.u8 0x00) (hash_len SHA2_256);
    B.fill rDigest (HI.u8 0x00) (hash_len SHA2_256);

  HST.pop_frame();
  C.EXIT_SUCCESS
