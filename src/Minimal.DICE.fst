/// Reference: https://github.com/microsoft/RIoT/blob/master/Reference/DICE/DiceCore.cpp
module Minimal.DICE

open LowStar.BufferOps
// open Lib.IntTypes
// open FStar.Integers

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

/// <><><><><><><><><><><><> DICE helpers <><><><><><><><><><><><><>

unfold inline_for_extraction noextract
let dice_hash (alg: dice_alg): hash_st alg =
  match alg with
  | SHA2_256 -> SHA2.hash_256
  | SHA2_384 -> SHA2.hash_384
  | SHA2_512 -> SHA2.hash_512
  | SHA1     -> SHA1.legacy_hash

unfold inline_for_extraction noextract
let dice_hmac (alg: dice_alg): HMAC.compute_st alg =
  match alg with
  | SHA2_256 -> HMAC.compute_sha2_256
  | SHA2_384 -> HMAC.compute_sha2_384
  | SHA2_512 -> HMAC.compute_sha2_512
  | SHA1     -> HMAC.legacy_compute_sha1

let rec pub_buffer_to_sec_l
  (size: I.uint_32)
  (#t: HI.inttype)
  (b_pub: B.buffer (HI.int_t t HI.PUB){B.length b_pub >= I.v size})
: HST.Stack (l_sec: list (HI.int_t t HI.SEC){List.length l_sec == I.v size})
  (requires fun h ->
    B.live h b_pub)
  (ensures  fun h0 l_sec h1 ->
    B.modifies B.loc_none h0 h1 /\
    I.v size == 0 ==> l_sec == Nil /\
    I.v size <> 0 ==>
    (let b_seq_pub = B.as_seq h0 b_pub in
     let b_of_size_seq_pub = Seq.slice b_seq_pub 0 (I.v size - 1) in
     let b_of_size_l_pub = Seq.seq_to_list b_of_size_seq_pub in
     let b_of_size_l_sec = List.mapT HI.(fun (s:int_t t PUB) -> cast t SEC s) b_of_size_l_pub in
     b_of_size_l_sec == l_sec))
=
  match size with
  | 0ul -> Nil
  |  _  -> let iterator = I.(size - 1ul) in
          let hd_pub = (B.index b_pub iterator) in
          let hd_sec = HI.cast t HI.SEC hd_pub in
          let tl_sec = pub_buffer_to_sec_l iterator b_pub in
          hd_sec :: tl_sec

/// <><><><><><><><><><><><> DICE main funtion <><><><><><><><><><><>

#reset-options "--z3rlimit 50"
let dice_main
  (st: state)
  (riot_size: riot_size_t)
  (riot_binary: B.buffer pub_uint8{B.length riot_binary == v riot_size})
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

  (**)let h0 = HST.get () in

  (* compute uDigest *)
  let uDigest: b:B.buffer uint8{B.length b == hash_length alg}
    = B.alloca (u8 0x00) digest_length in
  dice_hash alg
    uds uds_length
    uDigest;

  (**)let h1 = HST.get () in
  (**)assert (B.modifies (B.loc_buffer uDigest) h0 h1 /\
  (**)        B.as_seq h1 uDigest == Spec.Agile.Hash.hash alg (B.as_seq h0 uds));

  B.as_seq
  (* compute rDigest *)
  let riot_bianry_sec: b:B.buffer uint8{B.length b == v riot_size}
    = B.alloca (u8 0x00) riot_size in
  B.alloca_of_list
  let rDigest: b:B.buffer uint8{B.length b == hash_length alg}
    = B.alloca (u8 0x00) digest_length in
  dice_hash alg
    riot_binary riot_size
    rDigest;

  (**)let h2 = HST.get () in
  (**)assert (B.modifies (B.loc_buffer rDigest) h1 h2 /\
  (**)        B.as_seq h2 rDigest == Spec.Agile.Hash.hash alg (B.as_seq h1 riot_binary));

  (* compute cdi *)
  dice_hmac alg
    cdi
    uDigest digest_length
    rDigest digest_length;

  HST.pop_frame()

/// <><><><><><><><><><><><> C main funtion <><><><><><><><><><><>

assume val riot_size: riot_size_t

assume val riot_binary:
  b:B.buffer pub_uint8
    {B.length b == v riot_size /\
    (let (| _, _, local_st |) = local_state in
      B.loc_disjoint (B.loc_buffer b) (B.loc_mreference local_st))}

assume val safe_load
  (riot_size: riot_size_t)
  (riot_binary: B.buffer uint8{B.length riot_binary == v riot_size})
  (base_address: B.buffer pub_uint8)
: HST.Stack unit
  (requires fun h ->
    B.live h riot_binary /\
    B.live h base_address)
  (ensures  fun h0 _ h1 ->
    B.modifies (B.loc_buffer riot_binary) h0 h1)

// let riot_main_t =
//   (cdi: cdi_t)
// -> HST.Stack state
//   (requires fun h ->
//     B.live h cdi /\
//     uds_is_disabled)
//   (ensures  fun h0 _ h1 ->
//     let cdi = get_cdi st in
//       B.as_seq h1 cdi == Seq.create (v cdi_length) (u8 0x00))

// assume val riot_main: riot_main_t

// val safe_call
//     (riot_main: riot_main_t)
//     (st: state)
// : HST.Stack (st:state{B.all_disjoint ((get_loc_l st)@[B.loc_buffer riot_binary])})
//   (requires fun h ->
//     uds_is_disabled /\
//     h `B.live` riot_binary /\
//     (let (| _, _, local_st |) = local_state in
//       B.loc_disjoint (B.loc_buffer riot_binary) (B.loc_mreference local_st)))
//   (ensures  fun h0 _ h1 ->
//     B.live h1 riot_binary /\
//     uds_is_disabled)

// let safe_call riot_main st = riot_main st

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
    let st: st:state{B.all_disjoint ((get_loc_l st)@[B.loc_buffer riot_binary])}
      = initialize riot_binary in
    (* only allocating on the stack *)
    dice_main st riot_size riot_binary;

    (* wipe and disable uds *)
    unset_uds st;
    disable_uds st;
    C.EXIT_SUCCESS
  else
    C.EXIT_FAILURE
