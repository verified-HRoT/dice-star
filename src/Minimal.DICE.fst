/// Reference: https://github.com/microsoft/RIoT/blob/master/Reference/DICE/DiceCore.cpp
module Minimal.DICE

open LowStar.BufferOps
(* since there will be confusions about `cast` in both modules, I closed them for now *)
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

(* draft spec of public sequence to secret list conversion *)
let pub_to_sec_spec
  (size: I.uint_32{I.v size > 0})
  (#t: HI.inttype)
  (seq_pub: Seq.seq HI.(int_t t PUB){Seq.length seq_pub == I.v size})
  (seq_sec: Seq.seq HI.(int_t t SEC){Seq.length seq_sec == I.v size})
=
  let seq_of_size_pub = Seq.slice seq_pub 0 (I.v size - 1) in
  let l_of_size_pub = Seq.seq_to_list seq_of_size_pub in
  let l_of_size_sec = List.mapT HI.(fun (s:int_t t PUB) -> cast t SEC s) l_of_size_pub in
  Seq.seq_of_list l_of_size_sec == seq_sec

(* NEWLY defined mapping function without list *)
(* This seems fine, haven't tried in `dice_main` *)
(* NOTE: casting function for sec u8 to pub u8 is
   NOTE: `HI.(cast #U8 #PUB U8 SEC)` *)
let rec buffer_map_without_list
  (size: I.uint_32)
  (#t1 #t2: Type)
  (f: t1 -> t2)
  (b1: B.buffer t1{B.length b1 >= I.v size})
  (b2: B.buffer t2{B.length b2 >= I.v size})
: HST.Stack unit
  (requires fun h ->
    B.live h b1 /\
    B.live h b2
    (* no disjointness because it's ok to do something inplace *))
  (ensures  fun h0 _ h1 ->
    I.v size == 0 ==>
      B.modifies B.loc_none h0 h1 /\
    I.v size =!= 0 ==>
     (B.modifies (B.loc_buffer b2) h0 h1 /\
      List.mapT f (Seq.seq_to_list (Seq.slice (B.as_seq h0 b1) 0 (I.v size - 1)))
               == (Seq.seq_to_list (Seq.slice (B.as_seq h1 b2) 0 (I.v size - 1)))))
=
  match size with
  | 0ul -> ()
  |  _  -> let iterator = I.(size - 1ul) in
          let hd1 = B.index b1 iterator in
          B.upd b2 iterator (f hd1);
          buffer_map_without_list iterator f b1 b2

(* mapping function for the first `size` elements of a buffer, which returns a list as result *)
(* to avoid list and seq in computational code, I could rewrite it  *)
let rec buffer_map_l
  (size: I.uint_32)
  (#t1 #t2: Type)
  (f: t1 -> t2)
  (b1: B.buffer t1{B.length b1 >= I.v size})
: HST.StackInline (l2: list t2{List.length l2 == I.v size})
  (requires fun h ->
    B.live h b1)
  (ensures  fun h0 l2 h1 ->
    B.modifies B.loc_none h0 h1 /\
    I.v size == 0 ==> l2 == Nil /\
    I.v size =!= 0 ==>
        List.mapT f (Seq.seq_to_list (Seq.slice (B.as_seq h0 b1) 0 (I.v size - 1))) == l2)
    (decreases size)
=
  match size with
  | 0ul -> Nil
  |  _  -> let iterator = I.(size - 1ul) in
          let hd1 = (B.index b1 iterator) in
          let hd2 = f hd1 in
          let tl2 = buffer_map_l iterator f b1 in
          hd2 :: tl2

(* mapping function for the first `size` elements of a buffer, which uses `buffer_map_l` and returns a newly allocated buffer on caller's stack *)
(*
let buffer_map
  (size: I.uint_32{I.v size > 0})
  (#t1 #t2: Type)
  (f: t1 -> t2)
  (b1: B.buffer t1{B.length b1 >= I.v size})
: HST.StackInline (b2: B.buffer t2{B.length b2 == I.v size})
  (requires fun h ->
    B.live h b1)
  (ensures  fun h0 b2 h1 ->
    B.modifies B.loc_none h0 h1 /\
    B.live h1 b2 /\
    List.mapT f (Seq.seq_to_list (Seq.slice (B.as_seq h0 b1) 0 (I.v size - 1))) == Seq.seq_to_list (Seq.slice (B.as_seq h1 b2) 0 (I.v size - 1)))
=
  let l2: list _ = buffer_map_l size f b1 in
  let b2 = B.alloca_of_list l2 in
  b2
*)

/// <><><><><><><><><><><><> DICE main funtion <><><><><><><><><><><>

(* This old version `dice_on_stack` is for reference purpose, not what we want finally *)
(* F* warns when set `--query_stats` *)
#reset-options "--z3rlimit 30 --query_stats"
let dice_on_stack
  (st: state)
  (riot_size: riot_size_t)
  (riot_binary: B.buffer HI.uint8{B.length riot_binary == I.v riot_size})
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
  let uDigest: b:B.buffer HI.uint8{B.length b == hash_length alg}
    = B.alloca (HI.u8 0x00) digest_length in
  dice_hash alg
    uds uds_length
    uDigest;

  (**)let h1 = HST.get () in
  (**)assert (B.modifies (B.loc_buffer uDigest) h0 h1 /\
  (**)        B.as_seq h1 uDigest == Spec.Agile.Hash.hash alg (B.as_seq h0 uds));

  (* compute rDigest *)
  let rDigest: b:B.buffer HI.uint8{B.length b == hash_length alg}
    = B.alloca (HI.u8 0x00) digest_length in
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

(* This function is under working *)
(* I tried to use pub_uint8 buffer here and encountered many problems *)
(* I believe lots of these problems come from `Spec.Agile.HMAC.hmac` (used in our assertions and HACL functions), which used `pow2` in its precondition `keysized` *)
(* As we discussed, I should use `assert_norm` or some normalize ways to reduce `pow2` in F* *)
(* Now it is a mess *)
let dice_main
  (st: state)
  (riot_size: riot_size_t)
  (* here should be HI.pub_uint8 *)
  (riot_binary: B.buffer HI.uint8{B.length riot_binary == I.v riot_size})
: HST.Stack unit
  (requires fun h ->
    h `HWIface.contains` st /\
    h `B.live` riot_binary /\
    B.all_disjoint ((get_loc_l st)@[B.loc_buffer riot_binary]))
  (ensures  fun h0 _ h1 ->
    (let uds, cdi = get_uds st, get_cdi st in
     // let riot_binary_sec_l = pub_seq_to_sec_l_of_pos_size_spec riot_size (B.as_seq h0 riot_binary) in
       B.modifies (B.loc_buffer cdi) h0 h1 /\
       B.as_seq h1 cdi
         == Spec.Agile.HMAC.hmac alg
              (Spec.Agile.Hash.hash alg (B.as_seq h0 uds))
              (Spec.Agile.Hash.hash alg (B.as_seq h0 riot_binary))))
=
  HST.push_frame();
  let uds, cdi = get_uds st, get_cdi st in

  // (**)let h0 = HST.get () in
  let uDigest: b:B.buffer HI.uint8{B.length b == I.v digest_length} = B.alloca (HI.u8 0x00) digest_length
  in dice_hash alg uds uds_length uDigest;
  // (**)let h1 = HST.get () in
  // (**)assert (B.modifies (B.loc_buffer uDigest) h0 h1 /\
  // (**)        B.as_seq h1 uDigest == Spec.Agile.Hash.hash alg (B.as_seq h0 uds));

     (* here should allocate a secret riot_binary buffer *)
  // let riot_binary_sec = buffer_map riot_size HI.(cast #U8 #PUB U8 SEC) riot_binary in
  // (**)let h1 = HST.get () in
  let rDigest: b:B.buffer HI.uint8{B.length b == I.v digest_length} = B.alloca (HI.u8 0x00) digest_length
  in dice_hash alg riot_binary riot_size rDigest;
  // (**)let h2 = HST.get () in
  // (**)assert (B.modifies B.(loc_buffer rDigest) h1 h2 /\
  // (**)        B.as_seq h2 rDigest == Spec.Agile.Hash.hash alg (B.as_seq h1 riot_binary_sec));
  // (**)assert (Spec.Agile.HMAC.keysized alg (Seq.length (B.as_seq h2 uDigest)));
  (**)let h2 = HST.get () in
  (**)assert_norm (Spec.Agile.HMAC.keysized alg (Seq.length (B.as_seq h2 uDigest)));
  dice_hmac alg cdi uDigest digest_length rDigest digest_length;

  HST.pop_frame()

/// <><><><><><><><><><><><> C main funtion <><><><><><><><><><><>

assume val riot_size: riot_size_t

assume val riot_binary:
  b:B.buffer HI.pub_uint8
    {B.length b == I.v riot_size /\
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
  if (0 < I.v riot_size && I.v riot_size <= max_input_length alg) then
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
