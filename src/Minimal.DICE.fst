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

inline_for_extraction noextract
let dice_hash (alg: dice_alg): hash_st alg =
  match alg with
  | SHA2_256 -> SHA2.hash_256
  | SHA2_384 -> SHA2.hash_384
  | SHA2_512 -> SHA2.hash_512
  | SHA1     -> SHA1.legacy_hash

inline_for_extraction noextract
let dice_hmac (alg: dice_alg): HMAC.compute_st alg =
  match alg with
  | SHA2_256 -> HMAC.compute_sha2_256
  | SHA2_384 -> HMAC.compute_sha2_384
  | SHA2_512 -> HMAC.compute_sha2_512
  | SHA1     -> HMAC.legacy_compute_sha1

/// compute digest of `uds`
inline_for_extraction
let compute_uDigest
  (uDigest: B.buffer uint8{B.length uDigest == hash_length alg})
  (uds: B.buffer uint8{B.length uds == v uds_length})
: HST.StackInline unit
  (requires fun h ->
    B.all_live h [B.buf uDigest
                 ;B.buf uds] /\
    B.all_disjoint [B.loc_buffer uDigest
                   ;B.loc_buffer uds])
  (ensures  fun h0 _ h1 ->
    B.modifies (B.loc_buffer uDigest) h0 h1 /\
    B.as_seq h1 uDigest
      == Spec.Agile.Hash.hash alg (B.as_seq h0 uds))
=
  dice_hash alg
    uds
    uds_length
    uDigest

/// compute measurement of RIoT firmware
inline_for_extraction
let compute_rDigest
  (rDigest: B.buffer uint8{B.length rDigest == hash_length alg})
  (riot_size: riot_size_t)
  (riot_binary: B.buffer uint8 {B.length riot_binary == v riot_size})
: HST.StackInline unit
  (requires fun h ->
    B.all_live h [B.buf riot_binary
                 ;B.buf rDigest] /\
    B.all_disjoint [B.loc_buffer riot_binary
                   ;B.loc_buffer rDigest])
  (ensures  fun h0 _ h1 ->
    B.live h1 riot_binary /\
    B.modifies (B.loc_buffer rDigest) h0 h1 /\
    B.as_seq h1 rDigest
      == Spec.Agile.Hash.hash alg (B.as_seq h0 riot_binary))
=
  dice_hash alg
    riot_binary
    riot_size
    rDigest

/// Compute `cdi`
inline_for_extraction
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
    B.modifies (B.loc_buffer cdi) h0 h1 /\
    B.as_seq h1 cdi
      == Spec.Agile.HMAC.hmac alg (B.as_seq h0 uDigest) (B.as_seq h0 rDigest))
=
  (**)let h = HST.get() in
  (**)assert (Spec.Agile.HMAC.keysized alg (Seq.length (B.as_seq h uDigest)));
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
  (riot_size: riot_size_t)
  (riot_binary: B.buffer uint8 {B.length riot_binary == v riot_size})
: HST.Stack unit
  (requires fun h ->
    h `HWIface.contains` st /\
    h `B.live` riot_binary /\
    B.all_disjoint ((get_loc_l st)@[B.loc_buffer riot_binary]))
  (ensures  fun h0 _ h1 ->
    B.live h1 riot_binary /\
    (let uds, cdi = get_uds st, get_cdi st in
       B.modifies (B.loc_buffer cdi) h0 h1 /\
       B.as_seq h1 cdi
         == Spec.Agile.HMAC.hmac alg
              (Spec.Agile.Hash.hash alg (B.as_seq h0 uds))
              (Spec.Agile.Hash.hash alg (B.as_seq h0 riot_binary))))
=
  HST.push_frame();
  let uds, cdi = get_uds st, get_cdi st in

  (* compute digest of `uds` *)
  let uDigest: b:B.buffer uint8{B.length b == hash_length alg}
    = B.alloca (u8 0x00) digest_length
  in compute_uDigest uDigest uds;

  (* compute measurement of RIoT firmware *)
  let rDigest: b:B.buffer uint8{B.length b == hash_length alg}
    = B.alloca (u8 0x00) digest_length
  in compute_rDigest rDigest riot_size riot_binary;

  (* compute `cdi` *)
  dice_hmac alg
    cdi
    uDigest (hash_len alg)
    rDigest (hash_len alg);

  HST.pop_frame()

/// <><><><><><><><><><><><> DICE main funtion <><><><><><><><><><><>
/// DICE main function which has `ST` effect, can do heap and stack allocation
/// It allocates and manipulates in heap using hardware interface, and computes cdi on stack using the `dice_on_stack` function.

#reset-options "--z3rlimit 30"
let dice_main
  (riot_size: riot_size_t)
  (riot_binary: B.buffer uint8 {B.length riot_binary == v riot_size})
: HST.ST (st:state{B.all_disjoint ((get_loc_l st)@[B.loc_buffer riot_binary])})
  (requires fun h ->
    uds_is_uninitialized h /\
    h `B.live` riot_binary /\
    (let (| _, _, local_st |) = local_state in
      B.loc_disjoint (B.loc_buffer riot_binary) (B.loc_mreference local_st)))
  (ensures  fun h0 _ h1 ->
    uds_is_disabled)
=
  (* allocating in the heap *)
  let st = initialize riot_binary in

  (* only allocating on the stack *)
  dice_on_stack st riot_size riot_binary;

  (* wipe and disable uds *)
  unset_uds st;
  disable_uds st;

  (* FIXME: I failed to prove the liveness of `riot_binary` after freeing `uds` in `disable_uds`*)
  (**)//let h = HST.get () in
  (**)assert (B.disjoint riot_binary (get_uds st));
  (**)//assert (B.live h riot_binary);

  st

/// <><><><><><><><><><><><> C main funtion <><><><><><><><><><><>

assume val riot_size: riot_size_t

assume val riot_binary:
  b:B.buffer uint8
    {B.length b == v riot_size /\
    (let (| _, _, local_st |) = local_state in
      B.loc_disjoint (B.loc_buffer b) (B.loc_mreference local_st))}

let main ()
: HST.ST C.exit_code
  (requires fun h ->
    uds_is_uninitialized h /\
    B.live h riot_binary)
  (ensures  fun h0 _ h1 ->
    uds_is_disabled)
=
  (* Added a dynamic check, since we might assume `riot_size` in F*
     and computation relevant refinements on `riot_size` won't
     reach C code. Do we need it? *)
  if (0 < v riot_size && v riot_size <= max_input_length alg) then
    let st = dice_main riot_size riot_binary in
    C.EXIT_SUCCESS
  else
    C.EXIT_FAILURE
