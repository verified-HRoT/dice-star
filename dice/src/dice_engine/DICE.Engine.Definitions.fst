module DICE.Engine.Definitions

module HS = FStar.HyperStack

module I = Lib.IntTypes
module B = LowStar.Buffer

module S = Spec.Hash.Definitions
module H = Hacl.Hash.Definitions

open Lib.IntTypes

(*
 * Some common definitions used in the DICE code
 *)

#set-options "--__temp_no_proj DICE.Definitions"

let byte_sec = uint8
let byte_pub = pub_uint8

let bytes_sec = Seq.seq I.uint8
let bytes_pub = Seq.seq I.pub_uint8

let lbytes_sec = Seq.lseq I.uint8
let lbytes_pub = Seq.lseq I.pub_uint8

type dice_hash_alg = a:S.hash_alg{
  a =!= S.MD5 /\ a =!= S.SHA2_224 /\ a =!= S.Blake2S /\ a =!= S.Blake2B
}

inline_for_extraction
let alg : dice_hash_alg = S.SHA2_256

inline_for_extraction noextract
let dice_hash (alg:dice_hash_alg) : H.hash_st alg =
  match alg with
  | S.SHA2_256 -> Hacl.Hash.SHA2.hash_256
  | S.SHA2_384 -> Hacl.Hash.SHA2.hash_384
  | S.SHA2_512 -> Hacl.Hash.SHA2.hash_512
  | S.SHA1     -> Hacl.Hash.SHA1.legacy_hash

inline_for_extraction noextract
let dice_hmac (alg:dice_hash_alg) : Hacl.HMAC.compute_st alg =
  match alg with
  | S.SHA2_256 -> Hacl.HMAC.compute_sha2_256
  | S.SHA2_384 -> Hacl.HMAC.compute_sha2_384
  | S.SHA2_512 -> Hacl.HMAC.compute_sha2_512
  | S.SHA1     -> Hacl.HMAC.legacy_compute_sha1

unfold let digest_len = H.hash_len alg

unfold type digest_t = H.hash_t alg

unfold type hashable_len = i: size_t {0 < v i /\ v i <= S.max_input_length alg}
unfold type signable_len = i: size_t {64 + v i <= max_size_t}
unfold let cdi_len = digest_len


/// Some types used in the public key verification of the RIoT header

unfold type signature_t = B.lbuffer I.uint8 64
unfold type key_t = B.lbuffer I.uint8 32
