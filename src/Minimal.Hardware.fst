module Minimal.Hardware

open Lib.IntTypes

open Spec.Hash.Definitions
open Hacl.Hash.Definitions

module P = FStar.Preorder
module G = FStar.Ghost

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

module B = LowStar.Buffer

let uds_len = 0x20ul

noextract
type t =
  | Uninitialized
  | Enabled
  | Disabled

noextract
let t_rel : P.preorder (G.erased t) =
  fun x1 x2 ->
  match (G.reveal x1, G.reveal x2) with
  | Uninitialized, _
  | Enabled, Disabled -> True
  | _, _ -> x1 == x2

noextract
let local_state_ref : HST.mref (G.erased t) t_rel = HST.ralloc HS.root (G.hide Uninitialized)

let local_state = (| t, t_rel,  local_state_ref |)

let uds_is_uninitialized h =
  G.reveal (HS.sel h local_state_ref) == Uninitialized

noextract
let uds_is_initialized_predicate : HST.mem_predicate =
  fun h ->
  let x = G.reveal (HS.sel h local_state_ref) in
  x == Enabled \/ x == Disabled

let uds_is_initialized = HST.token_p local_state_ref uds_is_initialized_predicate

noextract
let uds_is_disabled_predicate : HST.mem_predicate =
  fun h -> G.reveal (HS.sel h local_state_ref) == Disabled

let uds_is_disabled = HST.token_p local_state_ref uds_is_disabled_predicate

noeq
type state = {
  uds     : B.buffer uint8;
  cdi     : B.buffer uint8;
  uds_val : s:G.erased (Seq.seq uint8){
    B.length uds == v uds_len /\
    B.length cdi == v cdi_len /\
    Seq.length (G.reveal s) == v uds_len /\
    B.freeable uds /\
    B.freeable cdi /\
    B.all_disjoint [ B.loc_buffer uds
                   ; B.loc_buffer cdi
                   ; B.loc_mreference local_state_ref]
  }
}

let get_uds st = st.uds
let get_cdi st = st.cdi
let get_uds_value st = G.reveal st.uds_val

let initialize riot_binary =
  HST.recall local_state_ref;
  local_state_ref `HST.op_Colon_Equals` (G.hide Enabled);
  HST.witness_p local_state_ref uds_is_initialized_predicate;

  let uds = B.malloc HS.root (u8 0x00) uds_len in
  let cdi = B.malloc HS.root (u8 0x00) uds_len in

  let uds_seq =
    let h = HST.get () in
    G.hide (B.as_seq h uds) in

  { uds = uds; cdi = cdi; uds_val = uds_seq }

let unset_uds st =
  let uds = get_uds st in
  B.fill uds (u8 0x00) uds_len;
  let h = HST.get () in
  assert (Seq.equal (B.as_seq h uds) (Seq.create (v uds_len) (u8 0x00)))

let disable_uds st =
  HST.recall_p local_state_ref uds_is_initialized_predicate;
  local_state_ref `HST.op_Colon_Equals` Disabled;
  HST.witness_p local_state_ref uds_is_disabled_predicate;

  B.free st.uds
