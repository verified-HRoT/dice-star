module Minimal.Loader

open LowStar.BufferOps
open Spec.Hash.Definitions
open Hacl.Hash.Definitions
open Lib.IntTypes

open Minimal.Hardware

module I  = FStar.Integers
module HI  = Lib.IntTypes

module SHA2       = Hacl.Hash.SHA2
module SHA1       = Hacl.Hash.SHA1
module MD5        = Hacl.Hash.MD5
module HMAC       = Hacl.HMAC
module Ed25519    = Hacl.Ed25519

module B   = LowStar.Buffer
module LB  = Lib.Buffer
module M   = LowStar.Modifies
module HS  = FStar.HyperStack
module HST = FStar.HyperStack.ST
module CString = C.String

let binary_len_t = a:size_t{0 < v a /\ v a <= max_input_length alg}

val header_len: binary_len_t

let version_number_t = pub_uint32
let signature_t = B.lbuffer uint8 64
let publickey_t = B.lbuffer uint8 32
let secretkey_t = B.lbuffer uint8 32
let msg_len_t = a:size_t{v a + 64 <= max_size_t}

let header_raw_t = B.lbuffer uint8 (v header_len)

(* ZT: plan to hide this definition in the next revision *)
noeq
type header_t = {
     (* actual entries in headers*)
     version        : version_number_t;
     binary_size    : riot_size_t;
     binary_hash    : digest_t;
     header_sig     : signature_t;
     (* extra entries for convenience *)
     binary         : B.lbuffer uint8 (v binary_size);
     header_raw     : header_raw_t;
     header_pubkey  : publickey_t
}

unfold noextract
let contains_header (h:HS.mem) (header: header_t) =
  B.live h header.binary_hash /\
  B.live h header.header_sig /\
  B.live h header.header_raw /\
  B.live h header.header_pubkey

unfold noextract
let get_header_loc_l header = [B.loc_buffer header.binary_hash
                               ;B.loc_buffer header.header_sig
                               ;B.loc_buffer header.header_raw
                               ;B.loc_buffer header.header_pubkey]

(* ZT: plan to revise this definition *)
val entry_t: Type0
val entry: entry_t

noeq
type layer_t = {
  size   : binary_len_t;
  binary : B.lbuffer uint8 (v size);
  entry  : entry_t
}

(* ZT: only thing in C *)
val load_header
  (_: unit)
: HST.ST (header: header_t)
  (requires fun h -> True)
  (ensures fun h0 header h1 -> B.(
    all_disjoint (get_header_loc_l header) /\
    modifies loc_none h0 h1 /\
    h1 `contains_header` header))

#reset-options "--z3rlimit 30"
let verify_header
  (header: header_t)
: HST.Stack bool
  (requires fun h ->
    h `contains_header` header /\
    B.all_disjoint (get_header_loc_l header))
  (ensures  fun h0 b h1 ->
    let rhDigest_seq = Spec.Agile.Hash.hash alg (B.as_seq h0 header.header_raw) in
    Spec.Ed25519.verify (B.as_seq h0 header.header_pubkey) rhDigest_seq (B.as_seq h0 header.header_sig) == b)
=
  HST.push_frame ();
  let rhDigest = B.alloca (u8 0x00) digest_len in
  dice_hash alg header.header_raw header_len rhDigest;
  let b = Ed25519.verify header.header_pubkey digest_len rhDigest header.header_sig in
  HST.pop_frame ();
  b

let load_layer
  (_: unit)
: HST.ST (layer: layer_t)
  (requires fun h -> True)
  (ensures  fun h0 layer h1 ->
    B.live h1 layer.binary)
=
  let header = load_header () in
  let layer: layer_t = {
    size   = header.binary_size;
    binary = B.malloc HS.root (u8 0x00) header.binary_size;
    entry  = entry } in
  let verify_result = verify_header header in
  (**)assume (verify_result == true);
  (**)assert (verify_result == true);
  (* ZT: no dynamic failures in F* *)
  if (verify_result) then () else (C.exit (-1l));
  layer
