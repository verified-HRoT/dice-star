module RIoT.Core

open RIoT.Stubs

open LowStar.BufferOps
open Lib.IntTypes
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
module MB  = LowStar.Monotonic.Buffer
module M   = LowStar.Modifies
module HS  = FStar.HyperStack
module HST = FStar.HyperStack.ST

/// <><><><><><><><<><><><><><> Stubs <><><><><><><><><><><><><><>
let _RIOT_ALG = SHA2_256

assume val signAliasCert
  (aliasKeyPub: riot_ecc_publickey)
  (deviceIDPub: riot_ecc_publickey)
  (fwidLen: I.uint_32)
  (fwid: B.lbuffer HI.uint8 (v fwidLen))
  (privKey: riot_ecc_privatekey)
: B.buffer HI.uint8

assume val signDeviceCert
  (deviceIDPub: riot_ecc_publickey)
  (rootKeyPub : option riot_ecc_publickey)
  (privKey: riot_ecc_privatekey)
: B.buffer HI.uint8
/// <><><><><><><><<><><><><><><><><><><><><><><><><><><><><><><><>
//#reset-options "--z3rlimit 100"
let riotStart
  (cdiLen: uint_32)
  (cdi : B.lbuffer uint8 (v cdiLen))
  (fwid: B.lbuffer uint8 (v _RIOT_DIGEST_LENGTH))
: HST.Stack unit
  (requires (fun h ->
      B.all_live h [B.buf cdi
                   ;B.buf fwid]
    /\ B.all_disjoint [B.loc_buffer cdi
                     ;B.loc_buffer fwid]
    /\ B.length cdi <= max_input_length _RIOT_ALG))
  (ensures  fun _ _ _ -> True)
=
  HST.push_frame();

  let cDigest : hash_t SHA2_256 = B.alloca (u8 0x00) _RIOT_DIGEST_LENGTH in
  let deviceIDPub: riot_ecc_publickey = {
    x = {bigval = B.alloca (u32 0x00) _BIGLEN};
    y = {bigval = B.alloca (u32 0x00) _BIGLEN};
    infinity = B.alloca (u32 0x00) 1ul
  } in
  let deviceIDPriv: riot_ecc_privatekey
    = {bigval = B.alloca (u32 0x00) _BIGLEN} in
  let aliasKeyPub: riot_ecc_publickey = {
    x = {bigval = B.alloca (u32 0x00) _BIGLEN};
    y = {bigval = B.alloca (u32 0x00) _BIGLEN};
    infinity = B.alloca (u32 0x00) 1ul
  } in
  let aliasKeyPriv: riot_ecc_privatekey
    = {bigval = B.alloca (u32 0x00) _BIGLEN} in
  let label_id = B.alloca (u8 0x00) _BIGLEN in
  let label_alias = B.alloca (u8 0x00) _BIGLEN in

/// Hash CDI to cDigest
  riotCrypt_Hash
    _RIOT_DIGEST_LENGTH cDigest
    cdiLen cdi;

/// Derive DeviceID Key pair
  riotCrypt_DeriveEccKey
    deviceIDPub
    deviceIDPriv
    _RIOT_ALG cDigest
    _BIGLEN label_id;

/// Combine CDI and FWID into cDigest
  riotCrypt_Hash2
    _RIOT_DIGEST_LENGTH cDigest
    _RIOT_DIGEST_LENGTH cDigest
    _RIOT_DIGEST_LENGTH fwid;

/// Derive aliaskey Key pair
  riotCrypt_DeriveEccKey
    aliasKeyPub
    aliasKeyPriv
    _RIOT_ALG cDigest
    _BIGLEN label_alias;

  let aliasCert =
    signAliasCert
      aliasKeyPub              // <-- AliasKey public key
      deviceIDPub              // <-- deviceID public key
      _RIOT_DIGEST_LENGTH fwid // <-- EXTENSION
      deviceIDPriv             // <-- SIGN
  in
  let deviceIDSelfCert =
    signDeviceCert
      deviceIDPub              // <-- deviceID public key
      None                     // <-- root public key
      deviceIDPriv             // <-- SIGN
  in

  HST.pop_frame()

let main ()
: HST.Stack C.exit_code
  (requires fun _ -> True)
  (ensures  fun _ _ _ -> True)
=
  C.EXIT_SUCCESS
