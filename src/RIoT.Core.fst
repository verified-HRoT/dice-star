module RIoT.Core

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

/// <><><><><><><><<><><><><><> Stubs <><><><><><><><><><><><><><>
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

/// <><><><><><><><<><><><><><><><><><><><><><><><><><><><><><><><>

#reset-options "--z3rlimit 100"
#push-options "--query_stats"
let riotStart
  (cdi: cdi_t)
: HST.Stack unit
  (requires (fun h ->
    B.live h cdi.cdi /\
    B.length cdi.cdi <= max_input_length cdi.alg))
  (ensures  fun _ _ _ -> True)
=
  HST.push_frame();

/// REF: BYTE                derBuffer[DER_MAX_TBS];
///      BYTE                cDigest[RIOT_DIGEST_LENGTH];
///      BYTE                FWID[RIOT_DIGEST_LENGTH];
///      RIOT_ECC_PRIVATE    deviceIDPriv;
///      RIOT_ECC_SIGNATURE  tbsSig;
///      DERBuilderContext   derCtx;
///      fpFirmwareEntry     FirmwareEntry;
///      BYTE               *fwImage;
///      uint32_t            length, PEMtype;
///      DWORD               fwSize, offset, i;
///      HINSTANCE           fwDLL;

  let cDigest : hash_t SHA2_256
    = B.alloca (u8 0x00) (hash_len SHA2_256) in

  riotCrypt_Hash
    (hash_len cdi.alg)
    cdi.cdi
    SHA2_256
    cDigest;

  HST.pop_frame()
