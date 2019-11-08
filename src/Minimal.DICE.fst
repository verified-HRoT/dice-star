/// Reference: https://github.com/microsoft/RIoT/blob/master/Reference/DICE/DiceCore.cpp
module Minimal.DICE

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

let _DICE_ALG = SHA2_256
let _DICE_UDS_LENGTH   : I.uint_32 = 0x20
let _DICE_DIGEST_LENGTH: I.uint_32 = hash_len _DICE_ALG

/// <><><><><><><><><><><><><> DICE Stubs <><><><><><><><><><><><><><><><>

assume val get_UDS
  (size: nat)
: HST.St (b:B.buffer HI.uint8 {B.length b = size})

assume val get_measurement
  (alg: hash_alg)
: HST.St (hash_t alg)

assume val diceSHA256
  (size : nat)
  (data: B.lbuffer HI.uint8 size)
  (digest: hash_t _DICE_ALG)
: HST.St unit

assume val diceSHA256_2
  (size1 : nat)
  (data1: B.lbuffer HI.uint8 size1)
  (size2 : nat)
  (data2 : B.lbuffer HI.uint8 size2)
  (digest: hash_t _DICE_ALG)
: HST.St unit

/// <><><><><><><><><><><><> DICE Core main funtion <><><><><><><><><><><>

#reset-options "--z3rlimit 10"
let diceStart ()
: HST.Stack (B.lbuffer HI.uint8 (v _DICE_DIGEST_LENGTH))
  (requires fun _ -> True)
  (ensures  fun _ _ _ -> True)
=
  HST.push_frame();

/// NOTE: compute digest `uDigest` of `uds`
  let uds : B.lbuffer HI.uint8 _DICE_UDS_LENGTH = get_UDS (v _DICE_UDS_LENGTH) in
  let uDigest :hash_t _DICE_ALG = B.alloca (HI.u8 0x00) _DICE_DIGEST_LENGTH in
    SHA2.hash_256
      uds
      _DICE_UDS_LENGTH
      uDigest;

/// NOTE: compute digest `rDigest` of `measurement`
  let measurement: hash_t _DICE_ALG = get_measurement _DICE_ALG in
  let rDigest :hash_t _DICE_ALG = B.alloca (HI.u8 0x00) _DICE_DIGEST_LENGTH in
    diceSHA256
      (v _DICE_DIGEST_LENGTH) measurement
      rDigest;

// NOTE: allocate cdi
    let cdi: hash_t _DICE_ALG
      = B.alloca (HI.u8 0x00) _DICE_DIGEST_LENGTH in

// NOTE: compute `cdi` from `uDigest` and `rDigest`
    diceSHA256_2
     (v _DICE_DIGEST_LENGTH) uDigest
     (v _DICE_DIGEST_LENGTH) rDigest
     cdi;

// NOTE: Zero-out `uDigest` and `rDigest`
    B.fill uDigest (HI.u8 0x00) _DICE_DIGEST_LENGTH;
    B.fill rDigest (HI.u8 0x00) _DICE_DIGEST_LENGTH;

  HST.pop_frame();

// NOTE: return `cdi`
  cdi
