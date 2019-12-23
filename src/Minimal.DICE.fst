/// Reference: https://github.com/microsoft/RIoT/blob/master/Reference/DICE/DiceCore.cpp
module Minimal.DICE

open LowStar.BufferOps
open Spec.Hash.Definitions
open Hacl.Hash.Definitions
open Lib.IntTypes
open LowStar.Failure

open Minimal.Hardware
//open Minimal.Loader

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


module HW = Minimal.Hardware

// /// <><><><><><><><><><><><> DICE main funtion <><><><><><><><><><><>

// #reset-options "--z3rlimit 30 --query_stats"
// let dice_main
//   (st: state)
// : HST.Stack unit
//   (requires fun h ->
//     h `contains` st)
//   (ensures  fun h0 _ h1 ->
//     (let uds, cdi = get_uds st, get_cdi st in
//      let riot_binary = get_binary (get_header st) in
//     (**)assert_norm (Spec.Agile.HMAC.keysized alg (v digest_len));
//     (**)assert_norm ((v digest_len) + block_length alg <= max_input_length alg);
//        B.modifies (B.loc_buffer cdi) h0 h1 /\
//        B.as_seq h1 cdi
//          == Spec.Agile.HMAC.hmac alg
//               (Spec.Agile.Hash.hash alg (B.as_seq h0 uds))
//               (Spec.Agile.Hash.hash alg (B.as_seq h0 riot_binary))))
// =
//   HST.push_frame();

//   let uds, cdi = get_uds st, get_cdi st in
//   let riot_size = get_binary_size (get_header st) in
//   let riot_binary = get_binary (get_header st) in
//   //   dice_main st riot.size riot.binary;

//   //   (* wipe and disable uds *)
//   //   unset_uds st;
//   //   disable_uds st;
//   //   C.EXIT_SUCCESS

//   (**)let h0 = HST.get () in

//   (* compute uDigest *)
//   let uDigest: b:B.buffer HI.uint8{B.length b == hash_length alg}
//     = B.alloca (HI.u8 0x00) digest_len in
//   dice_hash alg
//     uds uds_len
//     uDigest;

//   (**)let h1 = HST.get () in
//   (**)assert (B.modifies (B.loc_buffer uDigest) h0 h1 /\
//   (**)        B.as_seq h1 uDigest == Spec.Agile.Hash.hash alg (B.as_seq h0 uds));

//   (* compute rDigest *)
//   let rDigest: b:B.buffer HI.uint8{B.length b == hash_length alg}
//     = B.alloca (HI.u8 0x00) digest_len in
//   dice_hash alg
//     riot_binary riot_size
//     rDigest;

//   (**)let h2 = HST.get () in
//   (**)assert (B.modifies (B.loc_buffer rDigest) h1 h2 /\
//   (**)        B.as_seq h2 rDigest == Spec.Agile.Hash.hash alg (B.as_seq h1 riot_binary));

//   (* compute cdi *)
//   (**)assert_norm (Spec.Agile.HMAC.keysized alg (v digest_len));
//   dice_hmac alg
//     cdi
//     uDigest digest_len
//     rDigest digest_len;

//   HST.pop_frame()

// /// <><><><><><><><><><><><> C main funtion <><><><><><><><><><><>

// let main ()
// : HST.ST C.exit_code
//   (requires fun h ->
//     uds_is_uninitialized h)
//   (ensures  fun h0 _ h1 -> True \/
//     uds_is_disabled)
// =
//   let st = initialize () in
//   let header = get_header st in
//   let riot_size = get_binary_size header in
//   let verify_succeed = verify_header header in
//   if (verify_succeed) then
//   ( if ( (0ul <. riot_size) ) then
//     ( dice_main st
//     ; unset_uds st
//     ; disable_uds st )
//     else
//     ( failwith "RIoT size less than or equal 0" ) )
//   else
//   ( failwith "RIoT header verification failed" );

//   C.EXIT_SUCCESS

let compute_cdi (state:HW.state)
: HST.Stack C.exit_code
  (requires fun h ->
    h `HW.contains` state /\
    disjointness state /\
    B.as_seq h (HW.get_uds state) == HW.get_uds_value state)
  (ensures fun _ _ _ -> True)
= 


let dice_main ()
: HST.ST C.exit_code
  (requires fun h ->
    uds_is_uninitialized h)
  (ensures fun h0 _ h1 -> uds_is_disabled)
= let state = HW.initialize () in
  let _ = compute_cdi state in
  admit ()
