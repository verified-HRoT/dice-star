/// Reference: https://github.com/microsoft/RIoT/blob/master/Reference/RIoT/Core/RIoT.cpp
module Minimal.RIoT

open LowStar.BufferOps
open Lib.IntTypes
open FStar.Integers

open Spec.Hash.Definitions
open Hacl.Hash.Definitions

module I  = FStar.Integers
module HI  = Lib.IntTypes

module SHA2= Hacl.Hash.SHA2

module B   = LowStar.Buffer
module MB  = LowStar.Monotonic.Buffer
module M   = LowStar.Modifies
module HS  = FStar.HyperStack
module HST = FStar.HyperStack.ST

/// Hash algorithm for RIoT
let _RIOT_ALG = SHA2_256

/// Digest length for RIoT
let _RIOT_DIGEST_LENGTH: I.uint_32 = hash_len _RIOT_ALG

/// Definitions of ECC key pair
let _BIGLEN: I.uint_32 = 9ul
noeq
type bigval_t = {
     bigval : B.lbuffer HI.uint32 (v _BIGLEN)
  }

noeq
type affine_point_t = {
     x: bigval_t;
     y: bigval_t;
     infinity: B.pointer HI.uint32
  }

noeq
type ecdsa_sig_t = {
     r: bigval_t;
     s: bigval_t
  }

type ecc_signature  = ecdsa_sig_t
type ecc_privatekey = bigval_t
type ecc_publickey  = affine_point_t
type ecc_secret     = affine_point_t

type riot_ecc_signature  = ecc_signature
type riot_ecc_publickey  = ecc_publickey
type riot_ecc_privatekey = ecc_privatekey

/// <><><><><><><><<><><><> RIoT Stubs <><><><><><><><><><><><>
/// Abstract hash API for RIoT
assume val riotCrypt_Hash
  (resultSize: I.uint_32)
  (result: B.lbuffer HI.uint8 (I.v resultSize))
  (dataSize: I.uint_32)
  (data: B.lbuffer HI.uint8 (I.v dataSize))
: HST.St unit

/// Abstract hash API for RIoT, which takes two input datas
assume val riotCrypt_Hash2
  (resultSize: I.uint_32)
  (result: B.lbuffer HI.uint8 (I.v resultSize))
  (data1Size: I.uint_32)
  (data1: B.lbuffer HI.uint8 (I.v data1Size))
  (data2Size: I.uint_32)
  (data2: B.lbuffer HI.uint8 (I.v data2Size))
: HST.St unit

/// Abstract ECC key pair generation API for RIoT
assume val riotCrypt_DeriveEccKey
  (public_key : riot_ecc_publickey)
  (private_key: riot_ecc_privatekey)
  (digest_alg: hash_alg)
  (digest: hash_t digest_alg)
  (label_size: I.uint_32)
  (label: B.lbuffer HI.uint8 (I.v label_size))
: HST.St unit

/// Abstract AliasKey certificate generation API for RIoT
assume val signAliasCert
  (aliasKeyPub: riot_ecc_publickey)
  (deviceIDPub: riot_ecc_publickey)
  (fwidLen: I.uint_32)
  (fwid: B.lbuffer HI.uint8 (v fwidLen))
  (privKey: riot_ecc_privatekey)
: HST.St (B.buffer HI.uint8)

/// Abstract DeviceID certificate generation API for RIoT
assume val signDeviceCert
  (deviceIDPub: riot_ecc_publickey)
  (rootKeyPub : option riot_ecc_publickey)
  (privKey: riot_ecc_privatekey)
: HST.St (B.buffer HI.uint8)

/// Abstract API to get `FWID`, which is the measurement of the next layer
assume val get_FWID
  (u: unit)
: HST.St (B.lbuffer uint8 (v _RIOT_DIGEST_LENGTH))

///
/// <><><><><><><><<><><><> RIoT Start <><><><><><><><><><><><>
///
/// RIoT main function, which
/// 1. receives `CDI` from DICE
/// 2. gets `measurement` of the next layer using `API`
/// 3. generates DeviceID key pair
/// 4. generates AliasKey key pair
/// 5. generates certificates
///
#reset-options "--z3rlimit 20"
let riotStart
  (cdiLen: I.uint_32)
  (cdi : B.lbuffer HI.uint8 (v cdiLen))
: HST.St unit
=
  HST.push_frame();

/// allocation
  let fwid = get_FWID () in
  let cDigest : hash_t SHA2_256 = B.alloca (HI.u8 0x00) _RIOT_DIGEST_LENGTH in
  let deviceIDPub: riot_ecc_publickey = {
    x = {bigval = B.alloca (HI.u32 0x00) _BIGLEN};
    y = {bigval = B.alloca (HI.u32 0x00) _BIGLEN};
    infinity = B.alloca (HI.u32 0x00) 1ul
  } in
  let deviceIDPriv: riot_ecc_privatekey
    = {bigval = B.alloca (HI.u32 0x00) _BIGLEN} in
  let aliasKeyPub: riot_ecc_publickey = {
    x = {bigval = B.alloca (HI.u32 0x00) _BIGLEN};
    y = {bigval = B.alloca (HI.u32 0x00) _BIGLEN};
    infinity = B.alloca (HI.u32 0x00) 1ul
  } in
  let aliasKeyPriv: riot_ecc_privatekey
    = {bigval = B.alloca (HI.u32 0x00) _BIGLEN} in
  let label_id = B.alloca (HI.u8 0x00) _BIGLEN in
  let label_alias = B.alloca (HI.u8 0x00) _BIGLEN in

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

/// Generate `alias Cert`
  let aliasCert =
    signAliasCert
      aliasKeyPub              // <-- AliasKey public key
      deviceIDPub              // <-- deviceID public key
      _RIOT_DIGEST_LENGTH fwid // <-- EXTENSION
      deviceIDPriv             // <-- SIGN
  in

/// Generate self signed `deviceIDSelfCert`
  let deviceIDSelfCert =
    signDeviceCert
      deviceIDPub              // <-- deviceID public key
      None                     // <-- root public key
      deviceIDPriv             // <-- SIGN
  in

  HST.pop_frame()
