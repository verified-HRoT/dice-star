module HWAbstraction

module G = FStar.Ghost

module HS = FStar.HyperStack

open FStar.HyperStack.ST

module B = LowStar.Buffer
module IB = LowStar.ImmutableBuffer

module I = Lib.IntTypes

open FStar.Integers

open DICE.Definitions

friend HWState

let uds_len = 1ul

let uds_bytes = G.hide (Seq.create (v uds_len) (I.u8 0))

let uds : b:IB.ibuffer byte_sec{
  IB.frameOf b == HS.root /\
  IB.recallable b /\
  IB.length b == (v uds_len) /\
  IB.value_is b uds_bytes} =

  let uds = IB.igcmalloc HS.root (I.u8 0) uds_len in
  IB.witness_value uds;
  uds


let st : state =
  let l0_image_header_size = 1ul in
  let l0_binary_size = 1ul in
  let ghost_state = B.gcmalloc HS.root (G.hide (true, true)) 1ul in
  let cdi = B.gcmalloc HS.root (I.u8 0) digest_len in
  let l0_image_header = B.gcmalloc HS.root (I.u8 0) l0_image_header_size in
  let l0_image_header_sig = B.gcmalloc HS.root (I.u8 0) 64ul in
  let l0_binary = B.gcmalloc HS.root (I.u8 0) l0_binary_size in
  let l0_binary_hash = B.gcmalloc HS.root (I.u8 0) digest_len in
  let l0_image_auth_pubkey = B.gcmalloc HS.root (I.u8 0) 32ul in

  { ghost_state = ghost_state;
    cdi = cdi;
    l0_image_header_size = l0_image_header_size;
    l0_image_header = l0_image_header;
    l0_image_header_sig = l0_image_header_sig;
    l0_binary_size = l0_binary_size;
    l0_binary = l0_binary;
    l0_binary_hash = l0_binary_hash;
    l0_image_auth_pubkey = l0_image_auth_pubkey }

let uds_is_enabled h = b2t (fst (B.get h st.ghost_state 0))

let stack_is_erased h = b2t (snd (B.get h st.ghost_state 0))

let frame_ghost_state _ _ _ = ()

let read_uds uds_out =
  B.recall uds;
  IB.recall_value uds uds_bytes;
  B.blit uds 0ul uds_out 0ul uds_len

let disable_uds () =
  B.recall st.ghost_state;
  let old_val = B.index st.ghost_state 0ul in
  let new_val : (G.erased (bool & bool)) =
    let (b1, b2) = G.reveal old_val in
    G.hide (false, b2) in
  B.upd st.ghost_state 0ul new_val

let platform_zeroize_stack () =
  B.recall st.ghost_state;
  let old_val = B.index st.ghost_state 0ul in
  let new_val : (G.erased (bool & bool)) =
    let (b1, b2) = G.reveal old_val in
    G.hide (b1, true) in
  B.upd st.ghost_state 0ul new_val

let platform_zeroize len b =
  B.fill b (I.u8 0) len;
  let h = get () in
  assert (Seq.equal (Seq.slice (B.as_seq h b) 0 (UInt32.v len))
                    (B.as_seq h b))
