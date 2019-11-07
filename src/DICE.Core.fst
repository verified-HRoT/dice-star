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

module B   = LowStar.Buffer
module M   = LowStar.Modifies
module HS  = FStar.HyperStack
module HST = FStar.HyperStack.ST

/// dice hash algorithm
let _DICE_ALG = SHA2_256

/// <><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>

/// An API to get UDS.
/// REF: None
assume val get_UDS
  (size: nat)
: HST.Stack (b:B.buffer HI.uint8 {B.length b = size})
  (requires fun _ -> True)
  (ensures  fun h0 result h1 ->
      B.live h1 result)

assume val get_measurement
  (alg: hash_alg)
: HST.Stack (hash_t alg)
  (requires fun _ -> True)
  (ensures  fun h0 r h1 ->
      B.live h1 r)

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
  (digest: hash_t _DICE_ALG)
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

/// <><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>


/// DICE definitions
/// REF: #define DICE_UDS_LENGTH         0x20
///      #define DICE_DIGEST_LENGTH      0x20
let _DICE_UDS_LENGTH    = 0x20
let _DICE_DIGEST_LENGTH: uint_32 = hash_len _DICE_ALG



/// <><><><><><><><><><><><> DICE Core main funtion <><><><><><><><><><><>

#reset-options "--z3rlimit 10"
let main ()
: HST.Stack C.exit_code
  (requires fun _ -> True)
  (ensures  fun _ _ _ -> True)
=
  HST.push_frame();

/// NOTE: compute digest `uDigest` of `uds`
  let uds : B.lbuffer uint8 _DICE_UDS_LENGTH = get_UDS _DICE_UDS_LENGTH in
  let uDigest :hash_t _DICE_ALG = B.alloca (HI.u8 0x00) _DICE_DIGEST_LENGTH in
    SHA2.hash_256
      uds
      (u _DICE_UDS_LENGTH)
      uDigest;

/// NOTE: compute digest `rDigest` of `measurement`
  let measurement: hash_t _DICE_ALG = get_measurement _DICE_ALG in
  let rDigest :hash_t _DICE_ALG = B.alloca (HI.u8 0x00) _DICE_DIGEST_LENGTH in
    SHA2.hash_256
      measurement
      _DICE_DIGEST_LENGTH
      rDigest;

    let cdi: hash_t _DICE_ALG
      = B.alloca (HI.u8 0x00) _DICE_DIGEST_LENGTH in

    diceSHA256_2
     (v _DICE_DIGEST_LENGTH) uDigest
     (v _DICE_DIGEST_LENGTH) rDigest
     cdi;

    B.fill uDigest (HI.u8 0x00) _DICE_DIGEST_LENGTH;
    B.fill rDigest (HI.u8 0x00) _DICE_DIGEST_LENGTH;

  HST.pop_frame();
  C.EXIT_SUCCESS
