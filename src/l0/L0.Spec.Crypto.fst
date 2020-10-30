module L0.Spec.Crypto

module Fail = LowStar.Failure
module B = LowStar.Buffer
module IB = LowStar.ImmutableBuffer
module HS  = FStar.HyperStack
module HST = FStar.HyperStack.ST

module SHA1 = Hacl.Hash.SHA1
module SHA2 = Hacl.Hash.SHA2
module HMAC = Hacl.HMAC
module HKDF = Hacl.HKDF
module Ed25519 = Hacl.Ed25519
open Spec.Hash.Definitions
open Hacl.Hash.Definitions
open Lib.IntTypes

open L0.Base
open L0.Declassify

#set-options "--z3rlimit 64 --fuel 0 --ifuel 0"

unfold
let valid_hkdf_ikm_len
  (len: size_t)
= (* for Hacl.HKDF.extract_st *)
  v len + block_length alg < pow2 32 /\
  (* for Spec.Agile.HKDF.extract *)
  v len + block_length alg <= max_input_length alg

unfold
let valid_hkdf_lbl_len
  (len: size_t)
= (* for Hacl.HKDF.expand_st *)
  hash_length alg + v len + 1 + block_length alg < pow2 32 /\
  (* for Spec.Aigle.HKDF.expand *)
  hash_length alg + v len + 1 + block_length alg < max_input_length alg

(* Key Pair Derivation using HKDF and Ed25519
   See appendix below
 *)
let derive_sec_key_pair_spec
  (ikm_len: size_t { valid_hkdf_ikm_len ikm_len })
  (ikm: Seq.lseq uint8 (v ikm_len))
  (lbl_len: size_t { valid_hkdf_lbl_len lbl_len })
  (lbl: Seq.lseq uint8 (v lbl_len))
: GTot (Seq.lseq uint8 32 & Seq.lseq uint8 32)
= let alg = SHA2_256 in
  (* Derive private key from `ikm` and `lbl` using HKDF *)
  (* Step 1. extract a `prk` (Pseudo Random Key) from an empty `salt` of `hashLen` and `ikm` *)
  let salt = Seq.create (v (hash_len alg)) (u8 0x00) in
  let prk  = Spec.Agile.HKDF.extract
               (* alg *) alg
               (* salt*) salt
               (* ikm *) ikm in
  (* Step 2. expand `prk` and `lbl` to a `okm` (Output Keying Material) *)
  let private_key = Spec.Agile.HKDF.expand
                       (* alg *) alg
                       (* prk *) prk
                       (* info*) lbl
                       (* len *) (hash_length alg) in

  let public_key = Spec.Ed25519.secret_to_public private_key in

(* return *) (public_key, private_key)

let derive_key_pair_spec
  (ikm_len: size_t { valid_hkdf_ikm_len ikm_len })
  (ikm: Seq.lseq uint8 (v ikm_len))
  (lbl_len: size_t { valid_hkdf_lbl_len lbl_len })
  (lbl: Seq.lseq uint8 (v lbl_len))
: GTot (Seq.lseq pub_uint8 32 & Seq.lseq uint8 32)
= let public_key, private_key = derive_sec_key_pair_spec ikm_len ikm lbl_len lbl in
  let public_key = declassify_secret_bytes public_key in
(* return *) (public_key, private_key)

(* DeviceID Derivation
 *)
let derive_DeviceID_spec
  (cdi: lbytes_sec 32)
  (l0_label_DeviceID_len: size_t {valid_hkdf_lbl_len riot_label_DeviceID_len})
  (l0_label_DeviceID: lbytes_sec (v riot_label_DeviceID_len))
: GTot (lbytes_pub 32 & lbytes_sec 32)
= let cdigest = Spec.Agile.Hash.hash alg cdi in
  derive_key_pair_spec
    (* ikm *) 32ul cdigest
    (* lbl *) l0_label_DeviceID_len riot_label_DeviceID


(* AliasKey Derivation
 *)
let derive_AliasKey_spec
  (cdi: lbytes_sec 32)
  (fwid: lbytes_pub 32)
  (l0_label_AliasKey_len: size_t {valid_hkdf_lbl_len riot_label_AliasKey_len})
  (l0_label_AliasKey: lbytes_sec (v riot_label_AliasKey_len))
: GTot (lbytes_pub 32 & lbytes_sec 32)
= let cdigest = Spec.Agile.Hash.hash alg cdi in
  let adigest = Spec.Agile.HMAC.hmac alg cdigest (classify_public_bytes fwid) in
  derive_key_pair_spec
    (* ikm *) 32ul adigest
    (* lbl *) l0_label_AliasKey_len riot_label_AliasKey

let lemma_derive_authKeyID_length_valid ()
: Lemma ( 32 <= max_input_length Spec.Agile.Hash.SHA1 )
= assert_norm ( 32 <= max_input_length Spec.Agile.Hash.SHA1 )

let derive_authKeyID_spec
  (deviceIDPub: lbytes_sec 32)
: GTot (lbytes_pub 20)
= assert_norm (Seq.length deviceIDPub <= max_input_length Spec.Agile.Hash.SHA1);
  declassify_secret_bytes
    (Spec.Agile.Hash.hash
       Spec.Agile.Hash.SHA1
       deviceIDPub)

// let derive_authKeyID_from_cdi_spec
//   (cdi: lbytes_sec 32)
//   (l0_label_DeviceID_len: size_t {valid_hkdf_lbl_len riot_label_DeviceID_len})
//   (l0_label_DeviceID: lbytes_sec (v riot_label_DeviceID_len))
// : GTot (lbytes_pub 20)
// = let deviceID_pub_seq, deviceID_priv_seq = derive_sec_key_pair_spec
//                                                  (32ul) (Spec.Agile.Hash.hash alg cdi)
//                                                  (l0_label_DeviceID_len)
//                                                  (l0_label_DeviceID) in
//   derive_authKeyID_spec deviceID_pub_seq

(* Appendix:
                               RFC 5869: HKDF
  =======================================================================
2.2.  Step 1: Extract

   HKDF-Extract(salt, IKM) -> PRK

   Options:
      Hash     a hash function; HashLen denotes the length of the
               hash function output in octets

   Inputs:
      salt     optional salt value (a non-secret random value);
               if not provided, it is set to a string of HashLen zeros.
      IKM      input keying material

   Output:
      PRK      a pseudorandom key (of HashLen octets)

   The output PRK is calculated as follows:

   PRK = HMAC-Hash(salt, IKM)

2.3.  Step 2: Expand

   HKDF-Expand(PRK, info, L) -> OKM

   Options:
      Hash     a hash function; HashLen denotes the length of the
               hash function output in octets

   Inputs:
      PRK      a pseudorandom key of at least HashLen octets
               (usually, the output from the extract step)
      info     optional context and application specific information
               (can be a zero-length string)
      L        length of output keying material in octets
               (<= 255*HashLen)

   Output:
      OKM      output keying material (of L octets)
*)

(*                  RFC 8032 EdDSA: Ed25519 and Ed448
  =======================================================================
5.1.5.  Key Generation

   The private key is 32 octets (256 bits, corresponding to b) of
   cryptographically secure random data.  See [RFC4086] for a discussion
   about randomness.

   The 32-byte public key is generated by the following steps.

   1.  Hash the 32-byte private key using SHA-512, storing the digest in
       a 64-octet large buffer, denoted h.  Only the lower 32 bytes are
       used for generating the public key.

   2.  Prune the buffer: The lowest three bits of the first octet are
       cleared, the highest bit of the last octet is cleared, and the
       second highest bit of the last octet is set.

   3.  Interpret the buffer as the little-endian integer, forming a
       secret scalar s.  Perform a fixed-base scalar multiplication
       [s]B.

   4.  The public key A is the encoding of the point [s]B.  First,
       encode the y-coordinate (in the range 0 <= y < p) as a little-
       endian string of 32 octets.  The most significant bit of the
       final octet is always zero.  To form the encoding of the point
       [s]B, copy the least significant bit of the x coordinate to the
       most significant bit of the final octet.  The result is the
       public key.
*)
