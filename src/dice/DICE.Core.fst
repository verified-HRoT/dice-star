module DICE.Core

open LowStar.Comment

module Fail = LowStar.Failure
module B = LowStar.Buffer
module HS  = FStar.HyperStack
module HST = FStar.HyperStack.ST

open FStar.HyperStack.ST

open Lib.IntTypes
open Lib.ByteBuffer

module S = Spec.Hash.Definitions
module Ed25519 = Hacl.Ed25519

module HW = HWAbstraction

open DICE.Definitions

module HSeq = Lib.Sequence

module G = FStar.Ghost

open HWAbstraction

open HWState

let l0_image_is_valid (img:l0_image_t) (h:HS.mem) =
  Spec.Ed25519.verify
    (B.as_seq h img.l0_image_auth_pubkey)
    (B.as_seq h img.l0_image_header)
    (B.as_seq h img.l0_image_header_sig) /\

  Spec.Agile.Hash.hash alg (B.as_seq h img.l0_binary) ==
  B.as_seq h img.l0_binary_hash

inline_for_extraction
let verify_l0_image_hash (img:l0_image_t)
  : Stack bool
      (requires fun _ -> True)
      (ensures fun h0 b h1 ->
        B.(modifies loc_none h0 h1) /\
        (b <==> Spec.Agile.Hash.hash alg (B.as_seq h1 img.l0_binary) == B.as_seq h1 img.l0_binary_hash))
  = recall_image_liveness img;

    HST.push_frame ();

    let hash_buf = B.alloca (u8 0x00) digest_len in
    dice_hash alg
      (* msg *) img.l0_binary img.l0_binary_size
      (* dst *) hash_buf;
    let b = lbytes_eq #digest_len img.l0_binary_hash hash_buf in

    HST.pop_frame ();

    b

let authenticate_l0_image (img:l0_image_t)
  : Stack bool
      (requires fun _ -> True)
      (ensures fun h0 b h1 ->
        B.modifies B.loc_none h0 h1 /\
        (b <==> l0_image_is_valid img h1))
  = recall_image_liveness img;
    
    let valid_header_sig = Ed25519.verify
                           (* pub *) img.l0_image_auth_pubkey
                           (* msg *) img.l0_image_header_size img.l0_image_header
                           (* sig *) img.l0_image_header_sig in
    if valid_header_sig then verify_l0_image_hash img else false

let lemma_hmac_preconditions ()
  : Lemma
      (Spec.Agile.HMAC.keysized alg (v digest_len) /\
       v digest_len + S.block_length alg <= S.max_input_length alg)
  = assert_norm (Spec.Agile.HMAC.keysized alg (v digest_len) /\
               v digest_len + S.block_length alg <= S.max_input_length alg)


let cdi_functional_correctness (st:state) (h:HS.mem) =
  lemma_hmac_preconditions ();

  B.as_seq h st.cdi ==
  Spec.Agile.HMAC.hmac alg
    (Spec.Agile.Hash.hash alg uds_bytes)
    (Spec.Agile.Hash.hash alg (B.as_seq h st.l0.l0_binary))

#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
inline_for_extraction
let compute_cdi (st:state)
  : Stack unit
      (requires fun h ->
        st == HW.st () /\
        uds_is_enabled h /\
        Spec.Agile.Hash.hash alg (B.as_seq h st.l0.l0_binary) == B.as_seq h st.l0.l0_binary_hash)
      (ensures fun h0 _ h1 ->
        B.(modifies (loc_buffer st.cdi) h0 h1) /\
        cdi_functional_correctness st h1)
  = recall_st_liveness st;

    let h0 = get () in
    HST.push_frame ();

    let uds = B.alloca (u8 0x00) HW.uds_len in

     
    let h1 = get () in
    frame_ghost_state B.loc_none h0 h1;

    read_uds uds;

    let uds_digest = B.alloca (u8 0x00) digest_len in
    
    dice_hash alg uds uds_len uds_digest;
    
    (* Prf *) lemma_hmac_preconditions ();

    dice_hmac alg
      (* dst *) st.cdi
      (* key *) uds_digest digest_len
      (* msg *) st.l0.l0_binary_hash digest_len;

    zeroize uds_len uds;

    HST.pop_frame ()
#pop-options

type dice_return_code = | DICE_SUCCESS | DICE_ERROR

module ST = FStar.HyperStack.ST

unfold let all_heap_buffers_except_cdi_and_ghost_state_remain_same (h0 h1:HS.mem) =
  let s = st () in
  forall (a:Type0) (b:B.buffer a).
    (ST.is_eternal_region (B.frameOf b) /\
     B.disjoint b s.ghost_state /\
     B.disjoint b s.cdi /\
     B.live h0 b) ==> (B.as_seq h0 b == B.as_seq h1 b /\ B.live h1 b)

#push-options "--fuel 0 --ifuel 1"
let dice_main ()
  : Stack dice_return_code
    (requires fun h -> uds_is_enabled h)
    (ensures fun h0 r h1 ->
      (~ (uds_is_enabled h1)) /\
      stack_is_erased h1 /\
      all_heap_buffers_except_cdi_and_ghost_state_remain_same h0 h1 /\
      (r == DICE_SUCCESS <==> (l0_image_is_valid (st ()).l0 h1 /\ cdi_functional_correctness (st ()) h1)))
  = let s = HW.st () in
    recall_st_liveness s;
    let h0 = get () in
    let b = authenticate_l0_image s.l0 in
    let h1 = get () in
    frame_ghost_state B.loc_none h0 h1;
    let r = 
      if b then begin compute_cdi s; DICE_SUCCESS end
      else DICE_ERROR in
    let h2 = get () in
    frame_ghost_state (B.loc_buffer s.cdi) h1 h2;
    disable_uds ();
    platform_zeroize_stack ();
    r
#pop-options
