module DICE.Stubs

open Common

open LowStar.BufferOps
open FStar.Integers

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


/// An API to get UDS.
/// REF: None
assume val get_UDS
  (size: nat)
: HST.Stack (uds_t size)
  (requires fun _ -> True)
  (ensures  fun h0 uds h1 ->
      B.live h1 uds)


/// Function to load a library from an image path.
/// REF: None
assume val loadLibrary
  (path: string)
  (hDLL: hinstance)
: HST.Stack unit
  (requires fun h ->
      B.live h hDLL)
  (ensures fun h0 r h1 ->
      B.modifies (B.loc_buffer hDLL) h0 h1)


/// Get function pointer from a loaded library by an entry point.
/// REF: None
assume val getProcAddress
  (hDLL: hinstance)
  (entry: string)
: fpRiotStart


/// Get offset and size of RIoT Invariant Code.
/// REF: None
assume val diceGetRiotInfo
  (hDLL: hinstance)
  (offset: B.pointer I.uint_32)
  (riotSize: B.pointer nat)
: HST.Stack unit
  (requires fun h ->
      B.live h hDLL
    /\ B.live h offset
    /\ B.live h riotSize
    /\ B.disjoint hDLL offset
    /\ B.disjoint hDLL riotSize
    /\ B.disjoint riotSize offset)
  (ensures  fun h0 _ h1 ->
      B.modifies (B.loc_buffer offset) h0 h1
    /\ B.modifies (B.loc_buffer riotSize) h0 h1)


/// REF: void DiceSHA256 (
///        const uint8_t *buf,
///        size_t bufSize,
///        uint8_t *digest
///      )
assume val diceSHA256
  (#size : nat)
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
  (#size1 : nat)
  (data1: B.lbuffer HI.uint8 size1)
  (#size2 : nat)
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
