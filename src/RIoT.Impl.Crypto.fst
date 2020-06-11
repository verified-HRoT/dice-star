module RIoT.Impl.Crypto

module Fail = LowStar.Failure
module B = LowStar.Buffer
module IB = LowStar.ImmutableBuffer
module HS  = FStar.HyperStack
module HST = FStar.HyperStack.ST

module SHA2 = Hacl.Hash.SHA2
module HMAC = Hacl.HMAC
module HKDF = Hacl.HKDF
module Ed25519 = Hacl.Ed25519
open Spec.Hash.Definitions
open Hacl.Hash.Definitions
open Lib.IntTypes

open RIoT.Base
open RIoT.Declassify
open RIoT.Spec.Crypto

#set-options "--z3rlimit 64 --fuel 0 --ifuel 0"

let derive_key_pair
  (public_key : B.lbuffer pub_uint8 32)                 // Out
  (private_key: B.lbuffer uint8 32)                     // Out
                    (* NOTE Not using lbuffer here because lbuffer doesn't accept null *)
  (ikm_len: size_t) (ikm: B.buffer uint8 {B.length ikm == v ikm_len})  // In: Initial Data for derivation
  (lbl_len: size_t) (lbl: B.buffer uint8 {B.length lbl == v lbl_len})  // In: Label for derivation
: HST.Stack unit
  (requires fun h -> let alg = SHA2_256 in
    (* Separation Logic Properties *)
    B.live h ikm /\ B.live h lbl /\ B.live h public_key /\ B.live h private_key /\
    B.all_disjoint [B.loc_buffer ikm;
                    B.loc_buffer lbl;
                    B.loc_buffer public_key;
                    B.loc_buffer private_key] /\

    (* for Hacl.HKDF.extract_st *)
    v ikm_len + block_length alg < pow2 32 /\
    (* for Spec.Agile.HKDF.extract *)
    v ikm_len + block_length alg <= max_input_length alg /\
    (* for Hacl.HKDF.expand_st *)
    hash_length alg + v lbl_len + 1 + block_length alg < pow2 32 /\
    (* for Spec.Aigle.HKDF.expand *)
    hash_length alg + v lbl_len + 1 + block_length alg < max_input_length alg)
  (ensures  fun h0 _ h1 -> let alg = SHA2_256 in
    B.(modifies ((loc_buffer public_key) `loc_union` (loc_buffer private_key)) h0 h1) /\
   (let pub_seq, priv_seq = derive_key_pair_spec ikm_len (B.as_seq h0 ikm) lbl_len (B.as_seq h0 lbl) in
    B.as_seq h1 public_key == pub_seq /\ B.as_seq h1 private_key == priv_seq ))
= HST.push_frame ();

  (* NOTE:  Using SHA2_256 because Curve25519/Ed25519 requires a 32-bit private key *)
  [@inline_let] //AR: 06/11: blocking some reductions
  let alg = SHA2_256 in

  (* Using an empty (0x00) buffer of hashLen as salt. *)
  let salt: b:B.lbuffer uint8 32 {Spec.Agile.HMAC.keysized alg (B.length b)} = B.alloca (u8 0x00) (hash_len alg) in

  (* Derive private key from `ikm` and `lbl` using HKDF *)
  (* Step 1. extract a `prk` (Pseudo Random Key) from an empty `salt` of `hashLen` and `ikm` *)
  let prk : b:B.lbuffer uint8 32 {B.length b == hash_length alg} = B.alloca (u8 0x00) (hash_len alg) in
  HKDF.extract_sha2_256
    prk                 // out: Pseudo Random Key
    salt (hash_len alg) // in : (optional) Salt
    ikm  ikm_len;       // in : Input Keying Material

  (* Step 2. expand `prk` and `lbl` to a `okm` (Output Keying Material) *)
  (**)assert_norm (Spec.Agile.HMAC.keysized alg (hash_length alg));
  HKDF.expand_sha2_256
    private_key        // out: Output Keying Material
    prk (hash_len alg) // in : Pseudo Random Key
    lbl lbl_len        // in : (optional) Info
    (hash_len alg);    // in : okm len

  (* Derive public key from private key using Ed25519 (FIXME: Or Curve25519?) *)
  let secret_public_key: B.lbuffer uint8 32 = B.alloca (u8 0) 32ul in
  Ed25519.secret_to_public
    secret_public_key   // out: public
    private_key; // in : secret

  declassify_secret_buffer
    (* len *) 32ul
    (* src *) secret_public_key
    (* dst *) public_key;
  HST.pop_frame ()



let derive_DeviceID
  (deviceID_pub: B.lbuffer pub_uint8 32)
  (deviceID_priv: B.lbuffer uint8 32)
  // (cdi_len: hashable_len)
  (cdi: B.lbuffer uint8 32)
  (riot_label_DeviceID_len: size_t {valid_hkdf_lbl_len riot_label_DeviceID_len})
  (riot_label_DeviceID: B.lbuffer uint8 (v riot_label_DeviceID_len))
: HST.Stack (unit)
  (requires fun h ->
    B.(all_live h [buf deviceID_pub;
                   buf deviceID_priv;
                   buf cdi;
                   buf riot_label_DeviceID]) /\
    B.(all_disjoint [loc_buffer deviceID_pub;
                     loc_buffer deviceID_priv;
                     loc_buffer cdi;
                     loc_buffer riot_label_DeviceID]))
  (ensures fun h0 _ h1 ->
    B.(modifies (loc_buffer deviceID_pub `loc_union` loc_buffer deviceID_priv) h0 h1) /\
    ((B.as_seq h1 deviceID_pub <: lbytes_pub 32), (B.as_seq h1 deviceID_priv <: lbytes_sec 32)) ==
    derive_DeviceID_spec (B.as_seq h1 cdi) riot_label_DeviceID_len (B.as_seq h1 riot_label_DeviceID)
   )
= HST.push_frame ();
  let cDigest = B.alloca (u8 0) 32ul in
  riot_hash alg
    cdi 32ul
    cDigest;
  derive_key_pair
    deviceID_pub
    deviceID_priv
    32ul cDigest
    riot_label_DeviceID_len riot_label_DeviceID;
  HST.pop_frame ()

let derive_AliasKey
  (aliasKey_pub: B.lbuffer pub_uint8 32)
  (aliasKey_priv: B.lbuffer uint8 32)
  // (cdi_len: hashable_len)
  (cdi: B.lbuffer uint8 32)
  (fwid: B.lbuffer uint8 32)
  (riot_label_AliasKey_len: size_t {valid_hkdf_lbl_len riot_label_AliasKey_len})
  (riot_label_AliasKey: B.lbuffer uint8 (v riot_label_AliasKey_len))
: HST.Stack (unit)
  (requires fun h ->
    B.(all_live h [buf aliasKey_pub;
                   buf aliasKey_priv;
                   buf cdi;
                   buf fwid;
                   buf riot_label_AliasKey]) /\
    B.(all_disjoint [loc_buffer aliasKey_pub;
                     loc_buffer aliasKey_priv;
                     loc_buffer cdi;
                     loc_buffer fwid;
                     loc_buffer riot_label_AliasKey]))
  (ensures fun h0 _ h1 ->
    B.(modifies (loc_buffer aliasKey_pub `loc_union` loc_buffer aliasKey_priv) h0 h1) /\
    ((B.as_seq h1 aliasKey_pub  <: lbytes_pub 32),
     (B.as_seq h1 aliasKey_priv <: lbytes_sec 32)) == derive_AliasKey_spec
                                                        (B.as_seq h1 cdi)
                                                        (B.as_seq h1 fwid)
                                                        riot_label_AliasKey_len
                                                        (B.as_seq h1 riot_label_AliasKey) /\
    True
    )
= HST.push_frame ();
  let cDigest = B.alloca (u8 0) 32ul in
  riot_hash alg
    cdi 32ul
    cDigest;
  let aDigest = B.alloca (u8 0) 32ul in
  riot_hmac alg
    aDigest
    cDigest 32ul
    fwid    32ul;
  derive_key_pair
    aliasKey_pub
    aliasKey_priv
    32ul aDigest
    riot_label_AliasKey_len riot_label_AliasKey;
  HST.pop_frame ()
