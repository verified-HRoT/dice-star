module HWAbstraction

module G = FStar.Ghost

module HS = FStar.HyperStack

open FStar.HyperStack.ST

module B = LowStar.Buffer
module IB = LowStar.ImmutableBuffer

module I = Lib.IntTypes

open FStar.Integers

open DICE.Engine.Definitions

open HWState

val uds_len : hashable_len

val uds_bytes : s:G.erased bytes_sec{Seq.length (G.reveal s) == v uds_len}

val st (_:unit) : state

let st_liveness (st:state) (h:HS.mem) : Type0 =
  B.all_live h [
    B.buf st.ghost_state;
    B.buf st.cdi;
    B.buf st.l0.l0_image_header;
    B.buf st.l0.l0_image_header_sig;
    B.buf st.l0.l0_binary;
    B.buf st.l0.l0_binary_hash;
    B.buf st.l0.l0_image_auth_pubkey ]

inline_for_extraction noextract
let recall_image_liveness (img:l0_image_t)
  : Stack unit
      (requires fun _ -> True)
      (ensures fun h0 _ h1 ->
        h0 == h1 /\
        B.live h1 img.l0_image_header /\
        B.live h1 img.l0_image_header_sig /\
        B.live h1 img.l0_binary /\
        B.live h1 img.l0_binary_hash /\
        B.live h1 img.l0_image_auth_pubkey)
  = B.recall img.l0_image_header;
    B.recall img.l0_image_header_sig;
    B.recall img.l0_binary;
    B.recall img.l0_binary_hash;
    B.recall img.l0_image_auth_pubkey
  
inline_for_extraction noextract
let recall_st_liveness (st:state)
  : Stack unit
      (requires fun _ -> True)
      (ensures fun h0 _ h1 ->
        h0 == h1 /\
        st_liveness st h1)
  = B.recall st.ghost_state;
    B.recall st.cdi;
    B.recall st.l0.l0_image_header;
    B.recall st.l0.l0_image_header_sig;
    B.recall st.l0.l0_binary;
    B.recall st.l0.l0_binary_hash;
    B.recall st.l0.l0_image_auth_pubkey

val uds_is_enabled (h:HS.mem) : Type0

val stack_is_erased (h:HS.mem) : Type0

val frame_ghost_state (l:B.loc) (h0 h1:HS.mem)
  : Lemma
      (requires
        B.(loc_disjoint (loc_buffer (st ()).ghost_state) l) /\
        B.(modifies l h0 h1) /\
        B.live h0 (st ()).ghost_state)
      (ensures uds_is_enabled h0 == uds_is_enabled h1)

val read_uds (uds_out:B.lbuffer byte_sec (v uds_len))
  : Stack unit
      (requires fun h ->
        uds_is_enabled h /\
        B.live h uds_out /\
        HS.is_stack_region (B.frameOf uds_out))
      (ensures fun h0 _ h1 ->
        B.(modifies (loc_buffer uds_out) h0 h1) /\
        B.as_seq h1 uds_out == G.reveal uds_bytes)

val disable_uds (_:unit)
  : Stack unit
      (requires fun h -> uds_is_enabled h)
      (ensures fun h0 _ h1 ->
        (~ (uds_is_enabled h1)) /\
        B.(modifies (loc_buffer (st ()).ghost_state) h0 h1))

module ST = FStar.HyperStack.ST

unfold let all_heap_buffers_except_ghost_state_remain_same (h0 h1:HS.mem) =
  let s = st () in
  forall (a:Type0) (b:B.buffer a).
    (ST.is_eternal_region (B.frameOf b) /\
     B.disjoint b s.ghost_state /\
     B.live h0 b) ==> (B.as_seq h0 b == B.as_seq h1 b /\ B.live h1 b)

val platform_zeroize_stack (_:unit)
  : Stack unit
      (requires fun h -> ~ (uds_is_enabled h))
      (ensures fun h0 _ h1 ->
        (~ (uds_is_enabled h1)) /\
        stack_is_erased h1 /\
        all_heap_buffers_except_ghost_state_remain_same h0 h1)

val zeroize (len:I.size_t) (b:B.lbuffer byte_sec (v len))
  : Stack unit
      (requires fun h -> B.live h b)
      (ensures fun h0 _ h1 ->
        B.(modifies (loc_buffer b) h0 h1) /\
        B.as_seq h1 b == Seq.create (v len) (I.u8 0))
