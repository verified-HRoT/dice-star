module RIoT.Stubs

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

assume val riotCrypt_Hash
  (size: I.uint_32)
  (data: B.lbuffer uint8 (v size))
  (digest_alg: hash_alg)
  (digest: hash_t digest_alg)
: HST.Stack unit
  (requires fun h ->
      B.live h data
    /\ B.live h digest
    /\ B.disjoint data digest)
  (ensures  fun h0 _ h1 ->
      B.modifies (B.loc_buffer digest) h0 h1)

assume val riotCrypt_DeriveEccKey
  (public_key : riot_ecc_publickey)
  (private_key: riot_ecc_privatekey)
  (digest_alg: hash_alg)
  (digest: hash_t digest_alg)
  (label_size: I.uint_32)
  (label: B.lbuffer uint8 (I.v label_size))
: HST.Stack unit
  (requires fun h -> True)
  (ensures  fun h0 _ h1 -> True)
