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

#reset-options "--z3rlimit 30"
let verify_header
  (header: header_t)
: HST.Stack bool
  (requires fun h ->
    h `contains_header` header /\
    B.all_disjoint (get_header_loc_l header))
  (ensures  fun h0 b h1 ->
    let rhDigest_seq = Spec.Agile.Hash.hash alg (B.as_seq h0 (get_header_raw header)) in
    Spec.Ed25519.verify (B.as_seq h0 (get_header_pubkey header)) rhDigest_seq (B.as_seq h0 (get_header_sig header)) == b)
=
  HST.push_frame ();
  let rhDigest = B.alloca (u8 0x00) digest_len in
  dice_hash alg (get_header_raw header) header_len rhDigest;
  let b = Ed25519.verify (get_header_pubkey header) digest_len rhDigest (get_header_sig header) in
  HST.pop_frame ();
  b
