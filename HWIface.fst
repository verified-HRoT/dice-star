module HWIface

open FStar.Integers
open FStar.HyperStack.ST

module P = FStar.Preorder
module G = FStar.Ghost

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module B = LowStar.Buffer

let uds_length = 1ul

let cdi_length = 1ul

type t =
  | Uninitialized
  | Enabled
  | Disabled

let t_rel : P.preorder (G.erased t) =
  fun x1 x2 ->
  match (G.reveal x1, G.reveal x2) with
  | Uninitialized, _
  | Enabled, Disabled -> True
  | _, _ -> x1 == x2

let local_state_ref : ST.mref (G.erased t) t_rel = ST.ralloc HS.root (G.hide Uninitialized)

let local_state = (| t, t_rel,  local_state_ref |)

let uds_is_uninitialized h =
  G.reveal (HS.sel h local_state_ref) == Uninitialized

let uds_is_initialized_predicate : mem_predicate =
  fun h ->
  let x = G.reveal (HS.sel h local_state_ref) in
  x == Enabled \/ x == Disabled

let uds_is_initialized = token_p local_state_ref uds_is_initialized_predicate

let uds_is_disabled_predicate : mem_predicate =
  fun h -> G.reveal (HS.sel h local_state_ref) == Disabled

let uds_is_disabled = token_p local_state_ref uds_is_disabled_predicate

noeq
type state = {
  uds     : B.buffer uint_8;
  cdi     : B.buffer uint_8;
  uds_val : s:G.erased (Seq.seq uint_8){
    B.length uds == v uds_length /\
    B.length cdi == v cdi_length /\
    Seq.length (G.reveal s) == v uds_length /\
    B.freeable uds /\
    B.freeable cdi /\
    B.disjoint uds cdi /\
    B.(loc_disjoint (loc_buffer uds) (loc_mreference local_state_ref)) /\
    B.(loc_disjoint (loc_buffer cdi) (loc_mreference local_state_ref))
  }
}

let get_uds st = st.uds

let get_cdi st = st.cdi

let get_uds_value st = G.reveal st.uds_val

let initialize () =
  ST.recall local_state_ref;
  local_state_ref := Enabled;
  ST.witness_p local_state_ref uds_is_initialized_predicate;
  
  let uds = B.malloc HS.root 0uy uds_length in
  let cdi = B.malloc HS.root 0uy uds_length in

  let uds_seq =
    let h = ST.get () in
    G.hide (B.as_seq h uds) in

  { uds = uds; cdi = cdi; uds_val = uds_seq }

let unset_uds st = B.fill st.uds 0uy uds_length

let disable_uds st =
  ST.recall_p local_state_ref uds_is_initialized_predicate;
  local_state_ref := Disabled;
  ST.witness_p local_state_ref uds_is_disabled_predicate;

  B.free st.uds
