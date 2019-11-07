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
module MB  = LowStar.Monotonic.Buffer
module M   = LowStar.Modifies
module HS  = FStar.HyperStack
module HST = FStar.HyperStack.ST

/// <><><><><><><><<><><><><><> Stubs <><><><><><><><><><><><><><>

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

/// Don't use CDI directly
/// REF: RiotCrypt_Hash(cDigest, RIOT_DIGEST_LENGTH, CDI, CDILen);
  let cDigest : hash_t SHA2_256
    = B.alloca (u8 0x00) (hash_len SHA2_256) in

  riotCrypt_Hash
    (hash_len cdi.alg)
    cdi.cdi
    SHA2_256
    cDigest;

/// TODO: Set the serial number for DeviceID certificate
/// REF: RiotSetSerialNumber(&x509DeviceTBSData, cDigest, RIOT_DIGEST_LENGTH);
  let deviceIDPub: riot_ecc_publickey = {
    x = {data = B.alloca (u32 0x00) _BIGLEN};
    y = {data = B.alloca (u32 0x00) _BIGLEN};
    infinity = B.alloca (u32 0x00) 1ul
  } in

  let deviceIDPriv: riot_ecc_privatekey = {
    r = {data = B.alloca (u32 0x00) _BIGLEN};
    s = {data = B.alloca (u32 0x00) _BIGLEN}
  } in

  let data = B.alloca (u8 0x00) _BIGLEN in

  riotCrypt_DeriveEccKey
    deviceIDPub
    deviceIDPriv
    SHA2_256 cDigest
    _BIGLEN data;

  HST.pop_frame()
