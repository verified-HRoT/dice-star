module RIoT.Impl.Crypto

open LowStar.Comment
open LowStar.Printf
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

[@@ "opaque_to_smt"]
let derive_key_pair
  (public_key : B.lbuffer pub_uint8 32)                 // Out
  (private_key: B.lbuffer uint8 32)                     // Out
                    (* NOTE Not using lbuffer here because lbuffer doesn't accept ASN1_NULL *)
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


[@@ "opaque_to_smt"]
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

[@@ "opaque_to_smt"]
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

[@@ "opaque_to_smt"]
let derive_authKeyID
  (authKeyID: B.lbuffer byte_pub 20)
  (deviceIDPub: B.lbuffer byte_sec 32)
: HST.Stack unit
  (requires fun h ->
    B.live h authKeyID /\ B.live h deviceIDPub /\
    B.disjoint authKeyID deviceIDPub)
  (ensures fun h0 _ h1 ->
    B.modifies (B.loc_buffer authKeyID) h0 h1 /\
    B.as_seq h1 authKeyID == derive_authKeyID_spec (B.as_seq h0 deviceIDPub))
= HST.push_frame ();

  let authKeyID_sec = B.alloca (u8 0x00) 20ul in
  (* Prf *) lemma_derive_authKeyID_length_valid ();
  Hacl.Hash.SHA1.legacy_hash
    deviceIDPub 32ul
    authKeyID_sec;

  declassify_secret_buffer 20ul authKeyID_sec authKeyID;

  HST.pop_frame ()

[@@ "opaque_to_smt"]
unfold
let riot_core_step1_pre
  (h: HS.mem)
(* Inputs *)
  (cdi : B.lbuffer byte_sec 32)
  (fwid: B.lbuffer byte_sec 32)
  (deviceID_label_len: size_t)
  (deviceID_label: B.lbuffer byte_sec (v deviceID_label_len))
  (aliasKey_label_len: size_t)
  (aliasKey_label: B.lbuffer byte_sec (v aliasKey_label_len))
(* Outputs *)
  (deviceID_pub : B.lbuffer byte_pub 32)
  (deviceID_priv: B.lbuffer byte_sec 32)
  (aliasKey_pub : B.lbuffer byte_pub 32)
  (aliasKey_priv: B.lbuffer byte_sec 32)
  (authKeyID    : B.lbuffer byte_pub 20)
= B.(all_live h [buf cdi;
                 buf fwid;
                 buf deviceID_label;
                 buf aliasKey_label;
                 buf deviceID_pub;
                 buf deviceID_priv;
                 buf aliasKey_pub;
                 buf aliasKey_priv;
                 buf authKeyID]) /\
  B.(all_disjoint [loc_buffer cdi;
                   loc_buffer fwid;
                   loc_buffer deviceID_label;
                   loc_buffer aliasKey_label;
                   loc_buffer deviceID_pub;
                   loc_buffer deviceID_priv;
                   loc_buffer aliasKey_pub;
                   loc_buffer aliasKey_priv;
                   loc_buffer authKeyID]) /\
  valid_hkdf_lbl_len deviceID_label_len /\
  valid_hkdf_lbl_len aliasKey_label_len

[@@ "opaque_to_smt"]
unfold
let riot_core_step1_post
  (h0: HS.mem) (h1: HS.mem)
(* Inputs *)
  (cdi : B.lbuffer byte_sec 32)
  (fwid: B.lbuffer byte_sec 32)
  (deviceID_label_len: size_t)
  (deviceID_label: B.lbuffer byte_sec (v deviceID_label_len))
  (aliasKey_label_len: size_t)
  (aliasKey_label: B.lbuffer byte_sec (v aliasKey_label_len))
(* Outputs *)
  (deviceID_pub : B.lbuffer byte_pub 32)
  (deviceID_priv: B.lbuffer byte_sec 32)
  (aliasKey_pub : B.lbuffer byte_pub 32)
  (aliasKey_priv: B.lbuffer byte_sec 32)
  (authKeyID    : B.lbuffer byte_pub 20
              { riot_core_step1_pre (h0)
                     (cdi) (fwid)
                     (deviceID_label_len) (deviceID_label)
                     (aliasKey_label_len) (aliasKey_label)
                     (deviceID_pub) (deviceID_priv)
                     (aliasKey_pub) (aliasKey_priv)
                     (authKeyID) })
=
  // let deviceID_pub_seq, deviceID_priv_seq = derive_DeviceID_spec
  //                                             (B.as_seq h0 cdi)
  //                                             (deviceID_label_len)
  //                                             (B.as_seq h0 deviceID_label) in
  // let deviceID_pub_sec_seq = classify_public_bytes (B.as_seq h1 deviceID_pub) in
  (B.modifies (B.loc_buffer deviceID_pub  `B.loc_union`
               B.loc_buffer deviceID_priv `B.loc_union`
               B.loc_buffer aliasKey_pub  `B.loc_union`
               B.loc_buffer aliasKey_priv `B.loc_union`
               B.loc_buffer authKeyID) h0 h1) /\
  ((B.as_seq h1 deviceID_pub  <: lbytes_pub 32),
   (B.as_seq h1 deviceID_priv <: lbytes_sec 32)) == derive_DeviceID_spec
                                                      (B.as_seq h0 cdi)
                                                      (deviceID_label_len)
                                                      (B.as_seq h0 deviceID_label) /\
  ((B.as_seq h1 aliasKey_pub  <: lbytes_pub 32),
   (B.as_seq h1 aliasKey_priv <: lbytes_sec 32)) == derive_AliasKey_spec
                                                       (B.as_seq h0 cdi)
                                                       (B.as_seq h0 fwid)
                                                       (aliasKey_label_len)
                                                       (B.as_seq h0 aliasKey_label) /\
  (B.as_seq h1 authKeyID == derive_authKeyID_spec (classify_public_bytes (B.as_seq h1 deviceID_pub)))

#set-options "--z3rlimit 20 --fuel 0 --ifuel 0 --using_facts_from '* -FStar.Tactics -FStar.Reflection'"
[@@ "opaque_to_smt"]
inline_for_extraction
let riot_core_step1
(* Inputs *)
  (cdi : B.lbuffer byte_sec 32)
  (fwid: B.lbuffer byte_sec 32)
  (deviceID_label_len: size_t)
  (deviceID_label: B.lbuffer byte_sec (v deviceID_label_len))
  (aliasKey_label_len: size_t)
  (aliasKey_label: B.lbuffer byte_sec (v aliasKey_label_len))
(* Outputs *)
  (deviceID_pub : B.lbuffer byte_pub 32)
  (deviceID_priv: B.lbuffer byte_sec 32)
  (aliasKey_pub : B.lbuffer byte_pub 32)
  (aliasKey_priv: B.lbuffer byte_sec 32)
  (authKeyID    : B.lbuffer byte_pub 20)
: HST.Stack unit
  (requires fun h -> riot_core_step1_pre (h)
                     (cdi) (fwid)
                     (deviceID_label_len) (deviceID_label)
                     (aliasKey_label_len) (aliasKey_label)
                     (deviceID_pub) (deviceID_priv)
                     (aliasKey_pub) (aliasKey_priv)
                     (authKeyID))
  (ensures fun h0 _ h1 -> riot_core_step1_post (h0) (h1)
                     (cdi) (fwid)
                     (deviceID_label_len) (deviceID_label)
                     (aliasKey_label_len) (aliasKey_label)
                     (deviceID_pub) (deviceID_priv)
                     (aliasKey_pub) (aliasKey_priv)
                     (authKeyID))
= (**) let h0 = HST.get () in
  HST.push_frame ();
  (**) let hs0 = HST.get () in
  (**) B.fresh_frame_modifies h0 hs0;

(* Derive DeviceID *)
  // let deviceID_pub : B.lbuffer byte_pub 32 = B.alloca 0x00uy    32ul in
  // let deviceID_priv: B.lbuffer byte_sec 32 = B.alloca (u8 0x00) 32ul in
  let deviceID_pub_sec: B.lbuffer byte_sec 32 = B.alloca (u8 0x00) 32ul in
  printf "Deriving DeviceID\n" done;
  derive_DeviceID
    (* pub *) deviceID_pub
    (* priv*) deviceID_priv
    (* cdi *) cdi
    (* lbl *) deviceID_label_len
              deviceID_label;

  printf "Deriving AliasKey\n" done;
  derive_AliasKey
    (* pub *) aliasKey_pub
    (* priv*) aliasKey_priv
    (* cdi *) cdi
    (* fwid*) fwid
    (* lbl *) aliasKey_label_len
              aliasKey_label;

  classify_public_buffer 32ul deviceID_pub deviceID_pub_sec;

  derive_authKeyID
    authKeyID
    deviceID_pub_sec;

  (**) let hsf = HST.get () in
  HST.pop_frame ();
  (**) let hf = HST.get () in
  (**) B.popped_modifies hsf hf;
()

let lemma_riot_modifies
  (pub_t sec_t: Type0)
  (init_pub: pub_t) (init_sec: sec_t)
  (h0 hf: HS.mem)
  (deviceID_pub   : B.buffer pub_t)
  (aliasKey_pub   : B.buffer pub_t)
  (aliasKey_priv  : B.buffer sec_t)
  (deviceIDCSR_buf: B.buffer pub_t)
  (aliasKeyCRT_buf: B.buffer pub_t)
  (hs0 hs01 hs02 hs1 hs2 hs3 hsf: HS.mem)
  (_deviceID_priv : B.buffer sec_t)
  (_authKeyID     : B.buffer pub_t)
: Lemma
  (requires HS.fresh_frame h0 hs0 /\ HS.get_tip hs0 == HS.get_tip hsf /\ HS.popped hsf hf /\
            B.alloc_post_mem_common _deviceID_priv hs0  hs01 (Seq.create 32 init_sec) /\ B.frameOf _deviceID_priv == HS.get_tip hs0  /\
            B.alloc_post_mem_common _authKeyID     hs01 hs02 (Seq.create 20 init_pub) /\ B.frameOf _authKeyID     == HS.get_tip hs01 /\
            B.modifies (B.loc_buffer deviceID_pub   `B.loc_union`
                        B.loc_buffer _deviceID_priv `B.loc_union`
                        B.loc_buffer aliasKey_pub   `B.loc_union`
                        B.loc_buffer aliasKey_priv  `B.loc_union`
                        B.loc_buffer _authKeyID) hs02 hs1 /\
            B.modifies (B.loc_buffer deviceID_pub   `B.loc_union`
                        B.loc_buffer _deviceID_priv `B.loc_union`
                        B.loc_buffer aliasKey_pub   `B.loc_union`
                        B.loc_buffer aliasKey_priv  `B.loc_union`
                        B.loc_buffer _authKeyID     `B.loc_union`
                        B.loc_buffer deviceIDCSR_buf
                        ) hs1 hs2 /\
            B.modifies (B.loc_buffer deviceID_pub    `B.loc_union`
                        B.loc_buffer _deviceID_priv  `B.loc_union`
                        B.loc_buffer aliasKey_pub    `B.loc_union`
                        B.loc_buffer aliasKey_priv   `B.loc_union`
                        B.loc_buffer _authKeyID      `B.loc_union`
                        B.loc_buffer deviceIDCSR_buf `B.loc_union`
                        B.loc_buffer aliasKeyCRT_buf
                        ) hs2 hs3 /\
            hs3 == hsf)
  (ensures B.(modifies (loc_buffer deviceID_pub    `loc_union`
                        loc_buffer aliasKey_pub    `loc_union`
                        loc_buffer aliasKey_priv   `loc_union`
                        loc_buffer deviceIDCSR_buf `loc_union`
                        loc_buffer aliasKeyCRT_buf) h0 hf) )
= ()

