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

let (++) = List.append

/// compute digest of `uds`
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

/// compute measurement of RIoT firmware
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

///
/// if we treat `riot_t` as a argument of `dice_main`, then it will be allocated before we call `initialize ()` allocate `uds` and `cdi`, hence we cannot derive the disjointness between `riot.binary` and `uds` or `cdi`
///
/// Since we cannot directly allocate a buffer and "load" RIoT in F*, I will add a `riot_t` into hardware `state` and allocate it in the heap rather then on a stack.
///
/// DICE procedure on a stack
/// It has `Stack` effect, which can only do local stack allocations.
/// FIXME: Will stack be "clean"? Can I select all buffers on a stack frame?
#reset-options "--z3rlimit 30"
let dice_on_stack
  (st: state)
: HST.Stack unit
  (requires fun h ->
      B.all_live h (get_buf_t_l st)
    /\ B.all_disjoint (get_loc_l st))
  (ensures  fun h0 _ h1 ->
    let uds, cdi, riot = get_uds st, get_cdi st, get_riot st in
      B.modifies (B.loc_buffer cdi) h0 h1
    /\ B.as_seq h1 cdi
      == Spec.Agile.HMAC.hmac alg
           (Spec.Agile.Hash.hash alg (B.as_seq h0 uds))
           (Spec.Agile.Hash.hash alg (B.as_seq h0 riot.binary)))
=
  HST.push_frame();
  let uds, cdi, riot = get_uds st, get_cdi st, get_riot st in

  (* compute digest of `uds` *)
  let uDigest: b:B.buffer uint8{B.length b == hash_length alg}
    = B.alloca (u8 0x00) digest_length
  in compute_uDigest uDigest uds;

  (* compute measurement of RIoT firmware *)
  let rDigest: b:B.buffer uint8{B.length b == hash_length alg}
    = B.alloca (u8 0x00) digest_length
  in compute_rDigest rDigest riot;

  (* compute `cdi` *)
  compute_cdi cdi uDigest rDigest;

  HST.pop_frame()

/// <><><><><><><><><><><><> DICE main funtion <><><><><><><><><><><>
/// DICE main function which has `ST` effect, can do heap and stack allocation
/// It allocates and manipulates in heap using hardware interface, and computes cdi on stack using the `dice_on_stack` function.

#reset-options "--z3rlimit 30"
let dice_main
  (riot_size: riot_size_t)
: HST.ST unit
  (requires fun h ->
      uds_is_uninitialized h)
  (ensures  fun h0 _ h1 ->
      uds_is_disabled)
=
  (* allocating in the heap *)
  let st = initialize riot_size in

  (* only allocating on the stack *)
  dice_on_stack st;

  (* wipe and disable uds *)
  unset_uds st;
  disable_uds st

/// <><><><><><><><><><><><> C main funtion <><><><><><><><><><><>

let riot_size = 255ul

let main ()
: HST.ST C.exit_code
  (requires fun h ->
      uds_is_uninitialized h)
  (ensures  fun h0 _ h1 ->
      uds_is_disabled)
=
  dice_main riot_size;
  C.EXIT_SUCCESS
