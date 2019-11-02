module Common

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

/// An API to get UDS
type uds_t (size: nat) = B.lbuffer HI.uint8 size

/// CDI type, an alias of the hash digest type in Hacl*.
type cdi_t (alg: hash_alg) = hash_t alg

/// Handler/address for loaded libraries.
/// No reference code yet.
type hinstance = B.pointer HI.uint32

/// Function pointer to RiotStart function.
/// REF: typedef void(__cdecl* fpRiotStart)(const BYTE *, const uint32_t, const TCHAR *);
let fpRiotStart: Type0 =
#alg: hash_alg
-> cdi: cdi_t alg
-> HST.Stack unit
  (requires fun h ->
      B.live h cdi)
  (ensures  fun _ _ _ -> True)
