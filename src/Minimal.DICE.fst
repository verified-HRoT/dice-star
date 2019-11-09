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

/// Hash algorithm for dice
let _DICE_ALG = SHA2_256

/// Length of UDS for dice
let _DICE_UDS_LENGTH   : I.uint_32 = 0x20

/// Length of hash digest for dice
let _DICE_DIGEST_LENGTH: I.uint_32 = hash_len _DICE_ALG

/// <><><><><><><><><><><><><> DICE Stubs <><><><><><><><><><><><><><><><>

/// Abstract API to get `UDS`
assume val get_UDS
  (size: nat)
: HST.St (b:B.buffer HI.uint8 {B.length b = size})

/// Abstract API to get `measurement` of RIoT
assume val get_measurement
  (alg: hash_alg)
: HST.St (hash_t alg)

/// Abstract SHA2 256 hash API
assume val diceSHA256
  (size : nat)
  (data: B.lbuffer HI.uint8 size)
  (digest: hash_t _DICE_ALG)
: HST.St unit

/// Abstract SHA2 256 API, which takes two input datas
assume val diceSHA256_2
  (size1 : nat)
  (data1: B.lbuffer HI.uint8 size1)
  (size2 : nat)
  (data2 : B.lbuffer HI.uint8 size2)
  (digest: hash_t _DICE_ALG)
: HST.St unit

///
/// <><><><><><><><><><><><> DICE Core main funtion <><><><><><><><><><><>
///
/// DICE main function, which
/// 1. get `UDS` and `measurement` using API
/// 2. computes `CDI` and return it
/// 
let diceStart ()
: HST.Stack (B.lbuffer HI.uint8 (v _DICE_DIGEST_LENGTH))
  (requires fun _ -> True)
  (ensures  fun _ _ _ -> True)
=
  HST.push_frame();

/// Get `uds` and `measurement` using API
  let uds : B.lbuffer HI.uint8 _DICE_UDS_LENGTH = get_UDS (v _DICE_UDS_LENGTH) in
  let measurement: hash_t _DICE_ALG = get_measurement _DICE_ALG in

/// Allocate digests and `cdi`
  let uDigest :hash_t _DICE_ALG = B.alloca (HI.u8 0x00) _DICE_DIGEST_LENGTH in
  let rDigest :hash_t _DICE_ALG = B.alloca (HI.u8 0x00) _DICE_DIGEST_LENGTH in
  let cdi: hash_t _DICE_ALG = B.alloca (HI.u8 0x00) _DICE_DIGEST_LENGTH in

/// Compute digest `uDigest` of `uds`
    SHA2.hash_256
      uds
      _DICE_UDS_LENGTH
      uDigest;

/// compute digest `rDigest` of `measurement`
    diceSHA256
      (v _DICE_DIGEST_LENGTH) measurement
      rDigest;

/// compute `cdi` from `uDigest` and `rDigest`
    diceSHA256_2
     (v _DICE_DIGEST_LENGTH) uDigest
     (v _DICE_DIGEST_LENGTH) rDigest
     cdi;

/// Zero-out `uDigest` and `rDigest`
    B.fill uDigest (HI.u8 0x00) _DICE_DIGEST_LENGTH;
    B.fill rDigest (HI.u8 0x00) _DICE_DIGEST_LENGTH;

  HST.pop_frame();

/// return `cdi`
  cdi
