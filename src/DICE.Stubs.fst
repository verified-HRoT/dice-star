module DICE.Stubs

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


assume val loadLibrary
  (path: B.buffer imagePath)
  (hDLL: hinstance)
: HST.Stack unit
  (requires fun h ->
      B.live h path
    /\ B.live h hDLL.addr
    /\ B.disjoint path hDLL.addr)
  (ensures fun h0 r h1 ->
      B.modifies (B.loc_buffer hDLL.addr) h0 h1)

let fpRiotStart =
  (cdi: cdi_t)
-> HST.Stack unit
  (requires fun _ -> True)
  (ensures  fun _ _ _ -> True)

assume val getProcAddress
  (hDLL: hinstance)
  (entry: entryPoint)
: fpRiotStart

assume val diceGetRiotInfo
  (hDLL: hinstance)
  (offset: B.pointer I.uint_32)
  (riotSize: B.pointer nat)
: HST.Stack unit
  (requires fun h ->
      B.live h hDLL.addr
    /\ B.live h offset
    /\ B.live h riotSize
    /\ B.disjoint hDLL.addr offset
    /\ B.disjoint hDLL.addr riotSize
    /\ B.disjoint riotSize offset)
  (ensures  fun h0 _ h1 ->
      B.modifies (B.loc_buffer offset) h0 h1
    /\ B.modifies (B.loc_buffer riotSize) h0 h1)

assume val diceSHA256
  (size : nat)
  (data: B.lbuffer uint8 size)
  (digest: hash_t SHA2_256)
: HST.Stack unit
  (requires fun h ->
      B.live h data
    /\ B.live h digest
    /\ B.disjoint data digest)
  (ensures  fun h0 _ h1 ->
      B.modifies (B.loc_buffer digest) h0 h1)

assume val diceSHA256_2
  (size1 : nat)
  (data1: B.lbuffer uint8 size1)
  (size2 : nat)
  (data2 : B.lbuffer uint8 size2)
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

