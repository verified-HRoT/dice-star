/// Reference: https://github.com/microsoft/RIoT/blob/master/Reference/DICE/DiceCore.cpp
module Minimal.DICE

open LowStar.BufferOps
open Spec.Hash.Definitions
open Hacl.Hash.Definitions
open Lib.IntTypes

open Minimal.Hardware
open Minimal.Loader

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

/// <><><><><><><><><><><><> DICE main funtion <><><><><><><><><><><>

#reset-options "--z3rlimit 30 --query_stats"
let dice_main
  (st: state)
  (riot_size: riot_size_t)
  (riot_binary: B.buffer uint8{B.length riot_binary == v riot_size})
: HST.Stack unit
  (requires fun h ->
    h `contains` st /\
    h `B.live` riot_binary /\
    B.all_disjoint ((get_loc_l st)@[B.loc_buffer riot_binary]))
  (ensures  fun h0 _ h1 ->
    B.live h1 riot_binary /\
    (let uds, cdi = get_uds st, get_cdi st in
    (**)assert_norm (Spec.Agile.HMAC.keysized alg (v digest_len));
    (**)assert_norm ((v digest_len) + block_length alg <= max_input_length alg);
       B.modifies (B.loc_buffer cdi) h0 h1 /\
       B.as_seq h1 cdi
         == Spec.Agile.HMAC.hmac alg
              (Spec.Agile.Hash.hash alg (B.as_seq h0 uds))
              (Spec.Agile.Hash.hash alg (B.as_seq h0 riot_binary))))
=
  HST.push_frame();

  let uds, cdi = get_uds st, get_cdi st in

  (**)let h0 = HST.get () in

  (* compute uDigest *)
  let uDigest: b:B.buffer HI.uint8{B.length b == hash_length alg}
    = B.alloca (HI.u8 0x00) digest_len in
  dice_hash alg
    uds uds_len
    uDigest;

  (**)let h1 = HST.get () in
  (**)assert (B.modifies (B.loc_buffer uDigest) h0 h1 /\
  (**)        B.as_seq h1 uDigest == Spec.Agile.Hash.hash alg (B.as_seq h0 uds));

  (* compute rDigest *)
  let rDigest: b:B.buffer HI.uint8{B.length b == hash_length alg}
    = B.alloca (HI.u8 0x00) digest_len in
  dice_hash alg
    riot_binary riot_size
    rDigest;

  (**)let h2 = HST.get () in
  (**)assert (B.modifies (B.loc_buffer rDigest) h1 h2 /\
  (**)        B.as_seq h2 rDigest == Spec.Agile.Hash.hash alg (B.as_seq h1 riot_binary));

  (* compute cdi *)
  (**)assert_norm (Spec.Agile.HMAC.keysized alg (v digest_len));
  dice_hmac alg
    cdi
    uDigest digest_len
    rDigest digest_len;

  HST.pop_frame()

/// <><><><><><><><><><><><> C main funtion <><><><><><><><><><><>

// let riot_size: riot_size_t = 1ul

// assume val riot_binary:
//   b:B.buffer uint8
//     {B.length b == v riot_size /\
//     (let (| _, _, local_st |) = local_state in
//       B.loc_disjoint (B.loc_buffer b) (B.loc_mreference local_st))}


let main ()
: HST.ST C.exit_code
  (requires fun h ->
    uds_is_uninitialized h)
    // B.live h riot_binary)
  (ensures  fun h0 _ h1 -> True \/
    uds_is_disabled)
=
  let riot = Loader.load_layer () in
  (* ZT: do this for convenience now *)
  (**)let h = HST.get() in
  (**)assume (uds_is_uninitialized h);
  (**)assume (let (| _, _, local_st |) = local_state in
                  B.loc_disjoint (B.loc_buffer riot.binary) (B.loc_mreference local_st));

  C.String.print (C.String.of_literal "Test");

  (**)assert_norm ((max_input_length alg) <= maxint (len_int_type alg));
  if (0ul <. riot.size) then// && riot.size <=. (nat_to_len alg (max_input_length alg))) then
  (
    let st: st:state{B.all_disjoint ((get_loc_l st)@[B.loc_buffer riot.binary])}
      = initialize riot.binary in
    (* only allocating on the stack *)

    dice_main st riot.size riot.binary;

    (* wipe and disable uds *)
    unset_uds st;
    disable_uds st;
    C.EXIT_SUCCESS)
  else
    C.EXIT_FAILURE
