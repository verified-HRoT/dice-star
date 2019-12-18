module Minimal.Loader

open LowStar.BufferOps
open Spec.Hash.Definitions
open Hacl.Hash.Definitions
open Lib.IntTypes

open HWIface

module I  = FStar.Integers
module HI  = Lib.IntTypes

module SHA2       = Hacl.Hash.SHA2
module SHA1       = Hacl.Hash.SHA1
module MD5        = Hacl.Hash.MD5
module HMAC       = Hacl.HMAC
module Ed25519    = Hacl.Ed25519
// module Curve25519 = Hacl.Curve25519

module B   = LowStar.Buffer
module LB  = Lib.Buffer
module M   = LowStar.Modifies
module HS  = FStar.HyperStack
module HST = FStar.HyperStack.ST
module CString = C.String

let header_len = 1ul

let load_header
  (_: unit)
: HST.ST (header: header_t)
  (requires fun h -> True)
  (ensures fun h0 header h1 -> B.(
    all_disjoint (get_header_loc_l header) /\
    modifies loc_none h0 h1 /\
    h1 `contains_header` header))
=
  let version = uint #U32 #PUB 1 in
  let binary_size   = 100ul in
  let binary_hash   = B.malloc HS.root (u8 0x00) digest_len in
  let header_sig    = B.malloc HS.root (u8 0x00) 64ul in
  let binary        = B.malloc HS.root (u8 0x00) binary_size in
  let header_raw    = B.malloc HS.root (u8 0x00) header_len in
  let header_pubkey = B.malloc HS.root (u8 0x00) 32ul in
  { version     = version
  ; binary_size = binary_size
  ; binary_hash = binary_hash
  ; header_sig  = header_sig
  ; binary      = binary
  ; header_raw  = header_raw
  ; header_pubkey = header_pubkey}

