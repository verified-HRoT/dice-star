/// Reference: https://github.com/microsoft/RIoT/blob/master/Reference/DICE/DiceCore.cpp
module Minimal.DICE

open LowStar.BufferOps
open Lib.IntTypes
open FStar.Integers

open Spec.Hash.Definitions
open Hacl.Hash.Definitions

module I  = FStar.Integers
module HI  = Lib.IntTypes

module SHA2= Hacl.Hash.SHA2
module HMAC= Hacl.HMAC

module B   = LowStar.Buffer
module M   = LowStar.Modifies
module HS  = FStar.HyperStack
module HST = FStar.HyperStack.ST
module IB  = LowStar.ImmutableBuffer

/// Hash algorithm for dice
let _DICE_ALG = SHA2_256

/// Length of UDS for dice
let _DICE_UDS_LENGTH   : I.uint_32 = 0x20ul

/// Length of hash digest for dice
let _DICE_DIGEST_LENGTH: I.uint_32 = hash_len _DICE_ALG

/// <><><><><><><><><><><><><> Global Buffers <><><><><><><><><><><><><><><><>

///
/// A global secret eternal `uds` buffer
///
/// NOTE: We use `gcmalloc` to alloca "eternal" `uds` buffer, which must live (have property `recallable`), instead of using `malloc` to alloca "freeale" buffer, which can be hand-managed (have property `freeable`)
///
/// FIXME: Should I allocate them in a `main` function with `HST.ST` effect and then invoke `diceStart`? *)
///
/// FIXME: Must hand-retain the `recallable` property?
///
/// FIXME: Top-level let-bindings should have `Tot` effect, which may wipe properties like disjointness?

let uds
  : (b: B.buffer uint8 {B.length b = v _DICE_UDS_LENGTH /\ B.recallable b})
= B.gcmalloc HS.root (u8 0x00) _DICE_UDS_LENGTH

///
/// A global public eternal `measurement` buffer

let measurement
  : (b: hash_t _DICE_ALG {B.recallable b})
= B.gcmalloc HS.root (u8 0x00) _DICE_DIGEST_LENGTH

///
/// A global secret eternal `cdi` buffer

let cdi
  : (b: hash_t _DICE_ALG {B.recallable b})
= B.gcmalloc HS.root (u8 0x00) _DICE_DIGEST_LENGTH

/// <><><><><><><><><><><><> H/W API <><><><><><><><><><><><><><><><>

assume val uds_ghost: Ghost.erased (Seq.seq uint8)

///
/// H/W API which tells us whether the access of (H/W?) uds is disabled.
/// FIXME: How to define this?
assume val uds_is_disabled : Type0

assume val init_uds
  (u: unit)
: HST.Stack unit
  (requires fun h ->
    (* `uds` lives in h *)
      B.all_live h [B.buf uds]
    (* global buffers disjoint *)
    /\ B.all_disjoint [B.loc_buffer uds
                     ;B.loc_buffer measurement
                     ;B.loc_buffer cdi]
    )
  (ensures  fun h0 _ h1 ->
    (* only `uds` buffer is modified *)
      B.modifies (B.loc_buffer uds) h0 h1
    (* get the right `uds` *)
    (* FIXME: should I use `Ghost.reveal` here? *)
    /\ B.as_seq h1 uds == Ghost.reveal uds_ghost)

///
/// Data used to wipe `uds`

assume val irrelContent_as_list: list uint8
let irrelContent = Seq.seq_of_list irrelContent_as_list

///
/// API to wipe `uds` buffer and disable uds access.

assume val clear_and_disabled_uds
  (u: unit)
: HST.Stack unit
  (requires fun h ->
    (* `uds` lives in h *)
      B.all_live h [B.buf uds]
    (* global buffers disjoint *)
    /\ B.all_disjoint [B.loc_buffer uds
                     ;B.loc_buffer measurement
                     ;B.loc_buffer cdi]
    )
  (ensures  fun h0 _ h1 ->
    (* wiped `uds` buffer using some irrelevant content *)
      B.as_seq h1 uds == irrelContent
    (* the access of uds is disabled *)
    /\ uds_is_disabled
    (* only `uds` buffer is modified *)
    /\ B.modifies (B.loc_buffer uds) h0 h1)

/// <><><><><><><><><><><><><> DICE Stubs <><><><><><><><><><><><><><><><>

///
/// Compute `measurement`

let compute_measurement
  (riot_size: uint_32)
  (riot_binary: B.buffer uint8 {B.len riot_binary = riot_size})
: HST.Stack unit
  (requires fun h ->
    (* all buffers live in `h` *)
      B.all_live h [B.buf uds
                   ;B.buf measurement
                   ;B.buf cdi
                   ;B.buf riot_binary]
    (* all buffers disjoint *)
    /\ B.all_disjoint [B.loc_buffer uds
                     ;B.loc_buffer measurement
                     ;B.loc_buffer cdi
                     ;B.loc_buffer riot_binary]
    (* the length of `riot_binary` not exceeds the max input length of `SHA2.hash_256` *)
    /\ B.length riot_binary <= max_input_length SHA2_256
    )
  (ensures  fun h0 _ h1 ->
    (* only `measurement` buffer is modified *)
      B.modifies (B.loc_buffer measurement) h0 h1
    (* functional specification, actually already carried by `SHA2.hash_256` *)
    /\ B.as_seq h1 measurement
      == Spec.Agile.Hash.hash SHA2_256 (B.as_seq h0 riot_binary)
    )
=
  SHA2.hash_256
    riot_binary
    riot_size
    measurement

let uds_is_initialized h: Type0
=
  B.as_seq h uds == Ghost.reveal uds_ghost

///
/// Compute `cdi`

let compute_cdi
  (riot_size: uint_32)
  (riot_binary: B.buffer uint8 {B.len riot_binary = riot_size})
: HST.Stack unit
  (requires fun h ->
    (* all buffers live in `h` *)
      B.all_live h [B.buf uds
                   ;B.buf measurement
                   ;B.buf cdi
                   ;B.buf riot_binary]
    (* all buffers disjoint *)
    /\ B.all_disjoint [B.loc_buffer uds
                     ;B.loc_buffer measurement
                     ;B.loc_buffer cdi
                     ;B.loc_buffer riot_binary]
    (* the length of `riot_binary` not exceeds the max input length of `SHA2.hash_256` *)
    /\ B.length riot_binary <= max_input_length SHA2_256
    (* `uds` buffer is initialized *)
    /\ uds_is_initialized h
    )
  (ensures  fun h0 _ h1 ->
    (* only `measurement` buffer is modified *)
      B.modifies (B.loc_union_l [B.loc_buffer measurement
                                ;B.loc_buffer cdi]) h0 h1
    )
=
  compute_measurement riot_size riot_binary;
  HMAC.compute_sha2_256
    cdi
    uds         _DICE_UDS_LENGTH
    measurement _DICE_DIGEST_LENGTH


/// <><><><><><><><><><><><> DICE main funtion <><><><><><><><><><><>

let dice_main
  (riot_size: uint_32)
  (riot_binary: B.buffer uint8 {B.len riot_binary = riot_size})
: HST.Stack unit
  (requires fun h ->
    (* all buffers live in `h` *)
      B.all_live h [B.buf riot_binary]
    (* all buffers disjoint *)
    (* FIXME: How to retain or prove the disjointness of global buffers? *)
    /\ B.all_disjoint [B.loc_buffer uds
                     ;B.loc_buffer measurement
                     ;B.loc_buffer cdi
                     ;B.loc_buffer riot_binary]
    (* the length of `riot_binary` not exceeds the max input length of `SHA2.hash_256` *)
    /\ B.length riot_binary <= max_input_length SHA2_256
    )
  (ensures  fun h0 _ h1 -> True)
=
  (* retain liveness of global buffers *)
  B.recall uds;
  B.recall measurement;
  B.recall cdi;

  (* initialize `uds` *)
  init_uds ();

  (* compute `measurement` and `cdi` *)
  compute_cdi
    riot_size
    riot_binary;

  (* wipe `uds` buffer and disable uds access *)
  clear_and_disabled_uds ()

  // riot_main ()

/// <><><><><><><><><><><><> C main funtion <><><><><><><><><><><>

assume val riot_size: (i: uint_32 {v i <= max_input_length SHA2_256})
assume val riot_binary: (b: B.buffer uint8 {B.length b = v riot_size})

let main ()
: HST.St C.exit_code
=
  let h = HST.get () in
  assume (B.live h riot_binary);
  assume (B.all_disjoint [B.loc_buffer uds
                         ;B.loc_buffer measurement
                         ;B.loc_buffer cdi
                         ;B.loc_buffer riot_binary]);
  dice_main
    riot_size
    riot_binary;
  C.EXIT_SUCCESS
