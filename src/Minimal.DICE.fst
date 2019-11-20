/// Reference: https://github.com/microsoft/RIoT/blob/master/Reference/DICE/DiceCore.cpp
module Minimal.DICE

open LowStar.BufferOps
open Lib.IntTypes
open FStar.Integers

open Spec.Hash.Definitions
open Hacl.Hash.Definitions

open HWIface

module I  = FStar.Integers
module HI  = Lib.IntTypes

module SHA2= Hacl.Hash.SHA2
module SHA1= Hacl.Hash.SHA1
module MD5 = Hacl.Hash.MD5
module HMAC= Hacl.HMAC

module B   = LowStar.Buffer
module M   = LowStar.Modifies
module HS  = FStar.HyperStack
module HST = FStar.HyperStack.ST
module IB  = LowStar.ImmutableBuffer

/// <><><><><><><><><><><><><> Global Buffers <><><><><><><><><><><><><><><><>

/// <><><><><><><><><><><><> H/W API <><><><><><><><><><><><><><><><>
noeq
type riot_t = {
  size  : i: uint_32{v i <= max_input_length alg};
  binary: b: B.buffer uint8{B.length b == v size};
  entryPoint: Type0
}

/// <><><><><><><><><><><><><> DICE Stubs <><><><><><><><><><><><><><><><>

let dice_hash (alg: dice_alg): hash_st alg =
  match alg with
  | SHA2_256 -> SHA2.hash_256
  | SHA2_384 -> SHA2.hash_384
  | SHA2_512 -> SHA2.hash_512
  | SHA1     -> SHA1.legacy_hash

let dice_hmac (alg: dice_alg): HMAC.compute_st alg =
  match alg with
  | SHA2_256 -> HMAC.compute_sha2_256
  | SHA2_384 -> HMAC.compute_sha2_384
  | SHA2_512 -> HMAC.compute_sha2_512
  | SHA1     -> HMAC.legacy_compute_sha1

///
/// Compute `rDigest`
let (++) = List.append

let compute_uDigest
  (uDigest: B.buffer uint8{B.length uDigest == hash_length alg})
  (uds: B.buffer uint8{B.length uds == v uds_length})
: HST.StackInline unit
  (requires fun h ->
      B.all_live h [B.buf uDigest
                   ;B.buf uds]
    /\ B.all_disjoint [B.loc_buffer uDigest
                     ;B.loc_buffer uds])
  (ensures  fun h0 _ h1 ->
      B.modifies (B.loc_buffer uDigest) h0 h1
    /\ B.as_seq h1 uDigest
      == Spec.Agile.Hash.hash alg (B.as_seq h0 uds))
=
  dice_hash alg
    uds
    uds_length
    uDigest

let compute_rDigest
  (rDigest: B.buffer uint8{B.length rDigest == hash_length alg})
  (riot: riot_t)
: HST.StackInline unit
  (requires fun h ->
      B.all_live h [B.buf riot.binary
                   ;B.buf rDigest]
    /\ B.all_disjoint [B.loc_buffer riot.binary
                     ;B.loc_buffer rDigest])
  (ensures  fun h0 _ h1 ->
      B.modifies (B.loc_buffer rDigest) h0 h1
    /\ B.as_seq h1 rDigest
      == Spec.Agile.Hash.hash alg (B.as_seq h0 riot.binary))
=
  dice_hash alg
    riot.binary
    riot.size
    rDigest

///
/// Compute `cdi`

let compute_cdi
  (cdi: B.buffer uint8{B.length cdi == v cdi_length /\ B.freeable cdi})
  (uDigest: B.buffer uint8{B.length uDigest == hash_length alg})
  (rDigest: B.buffer uint8{B.length rDigest == hash_length alg})
: HST.StackInline unit
  (requires fun h ->
      B.all_live h [B.buf cdi
                   ;B.buf uDigest
                   ;B.buf rDigest]
    /\ B.all_disjoint [B.loc_buffer cdi
                     ;B.loc_buffer uDigest
                     ;B.loc_buffer rDigest])
  (ensures  fun h0 _ h1 ->
      B.modifies (B.loc_union_l [B.loc_buffer cdi]) h0 h1
    /\ B.as_seq h1 cdi
      == Spec.Agile.HMAC.hmac alg (B.as_seq h0 uDigest) (B.as_seq h0 rDigest))
=
  dice_hmac alg
    cdi
    uDigest (hash_len alg)
    rDigest (hash_len alg)

#reset-options "--z3rlimit 30"
let dice_on_stack
  (st: state)
  (riot: riot_t)
: HST.Stack unit
  (requires fun h ->
      B.all_live h (get_buf_t_l st ++ [B.buf riot.binary])
    /\ B.all_disjoint (get_loc_l st ++ [B.loc_buffer riot.binary]))
  (ensures  fun h0 _ h1 -> True)
    // let uds, cdi = get_uds st, get_cdi st in
    //   B.modifies (B.loc_buffer cdi) h0 h1
    // /\ B.as_seq h1 cdi
    //   == Spec.Agile.HMAC.hmac alg
    //        (Spec.Agile.Hash.hash alg (B.as_seq h0 uds))
    //        (Spec.Agile.Hash.hash alg (B.as_seq h0 riot.binary)))
=
  HST.push_frame();
  // let uds, cdi = get_uds st, get_cdi st in
  // let uDigest: b:B.buffer uint8{B.length b == hash_length alg}
  //   = B.alloca (u8 0x00) digest_length
  // in compute_uDigest uDigest uds;
  // let rDigest: b:B.buffer uint8{B.length b == hash_length alg}
  //   = B.alloca (u8 0x00) digest_length
  // in compute_rDigest rDigest riot;
  // compute_cdi cdi uDigest rDigest;
  HST.pop_frame()

/// <><><><><><><><><><><><> DICE main funtion <><><><><><><><><><><>
#reset-options "--z3rlimit 100"
// #push-options "--query_stats"
let dice_main
  (riot: riot_t)
: HST.ST unit
  (requires fun h ->
      uds_is_uninitialized h
    /\ B.live h riot.binary)
  (ensures  fun h0 _ h1 -> True)
=
  (* allocating in the heap *)
  let st = initialize () in

  (* only allocating on stack *)
  dice_on_stack st riot;

  (* wipe and disable uds *)
  // unset_uds st;
  // disable_uds st
  ()
/// <><><><><><><><><><><><> C main funtion <><><><><><><><><><><>

assume val riot_size: (i: uint_32 {v i <= max_input_length SHA2_256})
assume val riot_binary: (b: B.buffer uint8 {B.length b = v riot_size})

let main ()
: HST.St C.exit_code
=
  B.recall local_state_ref;
  let h = HST.get () in
  assume (B.live h riot_binary);
  assume (B.all_disjoint [B.loc_buffer uds
                         ;B.loc_buffer rDigest
                         ;B.loc_buffer cdi
                         ;B.loc_buffer riot_binary]);
  dice_main
    riot_size
    riot_binary;
  C.EXIT_SUCCESS
