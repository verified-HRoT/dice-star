module L0.Base

open LowStar.Comment

module Fail = LowStar.Failure
module B = LowStar.Buffer
module IB = LowStar.ImmutableBuffer
module HS  = FStar.HyperStack
module HST = FStar.HyperStack.ST

module SHA2 = Hacl.Hash.SHA2
module HMAC = Hacl.HMAC
module HKDF = Hacl.HKDF
// module ECDSA = Hacl.Impl.ECDSA
// module P256 = Hacl.Impl.P256
module Ed25519 = Hacl.Ed25519
module Curve25519 = Hacl.Curve25519_51

// module HW = HWAbstraction
open RIoT.Declassify
open Lib.IntTypes
open Spec.Hash.Definitions
open Hacl.Hash.Definitions
(*
 * Some common definitions used in the RIoT code
 *)

#set-options "--__temp_no_proj RIoT.Definitions"

type riot_hash_alg = a:hash_alg{a == SHA2_256}

inline_for_extraction
let alg : riot_hash_alg = SHA2_256

inline_for_extraction noextract
let riot_hash (alg:riot_hash_alg) : hash_st alg =
  match alg with
  | SHA2_256 -> Hacl.Hash.SHA2.hash_256
  | SHA2_384 -> Hacl.Hash.SHA2.hash_384
  | SHA2_512 -> Hacl.Hash.SHA2.hash_512
  // | SHA1     -> Hacl.Hash.SHA1.legacy_hash

inline_for_extraction noextract
let riot_hmac (alg:riot_hash_alg) : Hacl.HMAC.compute_st alg =
  match alg with
  | SHA2_256 -> Hacl.HMAC.compute_sha2_256
  | SHA2_384 -> Hacl.HMAC.compute_sha2_384
  | SHA2_512 -> Hacl.HMAC.compute_sha2_512
  // | SHA1     -> Hacl.HMAC.legacy_compute_sha1

unfold let digest_len = hash_len alg

unfold type digest_t = hash_t alg

unfold type hashable_len = i:size_t{0 < v i /\ v i <= max_input_length alg}

unfold let cdi_len = digest_len

unfold let byte_sec = uint8
unfold let byte_pub = pub_uint8

noextract unfold let bytes_pub  = Seq.seq byte_pub
noextract unfold let lbytes_pub = Seq.lseq byte_pub
noextract unfold let bytes_sec  = Seq.seq byte_sec
noextract unfold let lbytes_sec = Seq.lseq byte_sec

// #push-options "--z3rlimit 32"
// let label_DeviceID_l: list byte_sec = [u8 0; u8 0]
// let label_DeviceID_len
// : len: size_t { valid_hkdf_lbl_len len /\
//                 v len == List.length label_DeviceID_l }
// = assert_norm (valid_hkdf_lbl_len 2ul);
//   assert_norm (List.length label_DeviceID_l == 2);
//   2ul
// let label_DeviceID
// : ib:IB.libuffer uint8 (v label_DeviceID_len) (Seq.createL label_DeviceID_l)
//   { IB.frameOf ib == HS.root /\ IB.recallable ib /\
//     valid_hkdf_lbl_len (B.len ib) }
// = assert_norm (valid_hkdf_lbl_len label_DeviceID_len);
//   IB.igcmalloc_of_list HS.root label_DeviceID_l

// let label_AliasKey_l: list byte_sec = [u8 1; u8 1]
// let label_AliasKey_len
// : len: size_t { valid_hkdf_lbl_len len /\
//                 v len == List.length label_AliasKey_l }
// = assert_norm (valid_hkdf_lbl_len 2ul);
//   assert_norm (List.length label_AliasKey_l == 2);
//   2ul
// let label_AliasKey
// : ib:IB.libuffer uint8 (v label_AliasKey_len) (Seq.createL label_AliasKey_l)
//   { IB.frameOf ib == HS.root /\ IB.recallable ib /\
//     valid_hkdf_lbl_len (B.len ib) }
// = assert_norm (valid_hkdf_lbl_len label_AliasKey_len);
//   IB.igcmalloc_of_list HS.root label_AliasKey_l
// #push-options
