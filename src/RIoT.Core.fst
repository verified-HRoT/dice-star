/// Reference: https://github.com/microsoft/RIoT/blob/master/Reference/RIoT/Core/RIoT.cpp
module RIoT.Core

open LowStar.Comment

module Fail = LowStar.Failure
module B = LowStar.Buffer
module HS  = FStar.HyperStack
module HST = FStar.HyperStack.ST

open Lib.IntTypes
module S = Spec.Hash.Definitions
module H = Hacl.Hash.Definitions
module Ed25519 = Hacl.Ed25519
module Curve25519 = Hacl.Curve25519_51
module HKDF = Hacl.HKDF

module HW = HWAbstraction

open S
open H
open RIoT.Definitions

let salt_len: a:size_t{(v a) > 0 /\ Spec.Agile.HMAC.keysized alg (v a)}
  = 32ul
(* ZT: Hacl.HKDF.fsti and Spec.Agile.HKDF.fsti
       have different spec, I choose the smaller
       one `pow2 32` here*)
let info_len: a:size_t{(v a) > 0 /\ hash_length SHA2_256 + v a + 1 + block_length SHA2_256 <= pow2 32}
  = 32ul
let okm_len : a:size_t{(v a) > 0}
  = 32ul

#reset-options "--z3rlimit 30"
#push-options "--query_stats"
let riot_derive_key_pair
  (public_key: B.buffer uint8)
  (private_key: B.buffer uint8)
  (ikm: B.buffer uint8)
  (ikm_len: size_t)
: HST.Stack unit
  (requires fun h -> let alg = SHA2_256 in
    B.live h ikm /\ B.live h public_key /\ B.live h private_key /\
    B.all_disjoint [B.loc_buffer ikm; B.loc_buffer public_key; B.loc_buffer private_key] /\
    B.length ikm         == v ikm_len /\
    B.length public_key  == hash_length alg /\
    B.length private_key == hash_length alg /\
    (* `ikm` sepc required by `Hacl.HKDF.extract_st` *)
    v ikm_len + block_length alg < pow2 32 /\
    (* `ikm` spec required by `Spec.Agile.HKDF.extract` *)
    v ikm_len + block_length alg <= max_input_length alg /\
    (* `info` spec required by `Spec.Agile.HKDF.expand` *)
    hash_length alg + v info_len + 1 + block_length alg <= max_input_length alg) //pow2 61 -1
  (ensures  fun h0 _ h1 -> let alg = SHA2_256 in
    B.(modifies ((loc_buffer public_key) `loc_union` (loc_buffer private_key)) h0 h1) /\
    B.(let salt = (Seq.create (v salt_len) (u8 0x00)) in
       let info = (Seq.create (v info_len) (u8 0x00)) in
       let prk = Spec.Agile.HKDF.extract alg salt (as_seq h0 ikm) in
       as_seq h1 private_key == Spec.Agile.HKDF.expand alg prk info (hash_length alg)) /\
    B.(as_seq h1 public_key == Spec.Curve25519.secret_to_public (as_seq h1 private_key)))
=
  HST.push_frame ();
  let alg = SHA2_256 in
  let prk : b:B.buffer uint8{B.length b == hash_length alg} = B.alloca (u8 0x00) (hash_len alg) in
  let salt: b:B.buffer uint8{Spec.Agile.HMAC.keysized alg (B.length b)} = B.alloca (u8 0x00) salt_len in
  HKDF.extract_sha2_256
    prk           // out: Pseudo Random Key
    salt salt_len // in : (optional) Salt
    ikm  ikm_len; // in : Input Keying Material
  let info: b:B.buffer uint8{B.length b == v info_len} = B.alloca (u8 0x00) info_len in
  (**)assert_norm (Spec.Agile.HMAC.keysized alg (hash_length alg));
  HKDF.expand_sha2_256
    private_key        // out: Output Keying Material
    prk (hash_len alg) // in : Pseudo Random Key
    info info_len      // in : (optional) Info
    (hash_len alg);    // in : okm len
  Curve25519.secret_to_public
    public_key   // out: public
    private_key; // in : secret
  HST.pop_frame ()

noeq
type cert_t = {
  tbs: B.lbuffer uint8 32;
  sig: B.lbuffer uint8 64
}

unfold
let contains_cert h cert =
  B.live h cert.tbs /\
  B.live h cert.sig

unfold
let get_cert_loc_l cert = [
  B.loc_buffer cert.tbs;
  B.loc_buffer cert.sig
]

noeq
type riot_out_t = {
     // alias_public_key    : B.lbuffer uint8 32;
     // alias_private_key   : B.lbuffer uint8 32;
     deviceID_public_key : B.lbuffer uint8 32;
     deviceID_cert        : cert_t
}

unfold
let contains_riot_out (h: HS.mem) (rout: riot_out_t) =
  // B.live h rout.alias_public_key /\
  // B.live h rout.alias_private_key /\
  B.live h rout.deviceID_public_key /\
  h `contains_cert` rout.deviceID_cert

unfold
let get_riot_out_loc_l rout = [
   // B.loc_buffer rout.alias_public_key;
   // B.loc_buffer rout.alias_private_key;
   B.loc_buffer rout.deviceID_public_key
] @ (get_cert_loc_l rout.deviceID_cert)

#reset-options "--z3rlimit 50"
#push-options "--query_stats"
let riot_main
  (st: HW.state)
  (fwid: B.buffer uint8{B.length fwid == v digest_len})
  (rout:riot_out_t)
: HST.Stack unit
  (requires fun h ->
    B.live h (HW.get_cdi st) /\
    B.live h fwid /\
    h `contains_riot_out` rout /\
    B.all_disjoint ((get_riot_out_loc_l rout)@[B.loc_buffer (HW.get_cdi st); B.loc_buffer fwid]))
  (ensures  fun h0 _ h1 ->
    B.(modifies (loc_union_l (get_riot_out_loc_l rout)) h0 h1) /\
    (* TODO: spec for RIoT main *) True)
=
  HST.push_frame ();
  let cdi = HW.get_cdi st in
  let cDigest: b:B.buffer uint8{B.length b == v digest_len} = B.alloca (u8 0) digest_len in
  (**)assert_norm (v digest_len <= max_input_length alg);
  riot_hash alg
    cdi cdi_len    //in : data
    cDigest;       //out: digest
  let deviceID_private_key: b:B.buffer uint8{B.length b == v digest_len} = B.alloca (u8 0) digest_len in
  (**)assert_norm (v digest_len + block_length alg <= max_input_length alg);
  riot_derive_key_pair
    rout.deviceID_public_key //out: public key
    deviceID_private_key     //out: private key
    cDigest digest_len;      //in :ikm

  (* NOTE: Now I just fill the public key into the To-Be-Signed region *)
  B.blit
    rout.deviceID_public_key 0ul
    rout.deviceID_cert.tbs   0ul
    32ul;
  Ed25519.sign
    rout.deviceID_cert.sig  //out: signature
    deviceID_private_key    //in : secret
    32ul                    //in : msglen
    rout.deviceID_cert.tbs; //in : msg

  (* FIXME: just consider deviceID now *)
  // (* NOTE: hmac requires disjointness *)
  // let cfDigest: b:B.buffer uint8{B.length b == v digest_len} = B.alloca (u8 0) digest_len in
  // riot_hmac alg
  //   cfDigest            //out: tag
  //   cDigest digest_len  //in : key
  //   fwid    digest_len; //in : data
  // riot_derive_key_pair
  //   rout.alias_public_key  //out: public key
  //   rout.alias_private_key //out: private key
  //   cfDigest digest_len;   //in :ikm

  HST.pop_frame ()
