module HWAbstraction

module P = FStar.Preorder
module G = FStar.Ghost

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

module B = LowStar.Buffer

let uds_len = 0x20ul

#set-options "--max_fuel 0 --ifuel 2"

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


let local_state_ref : HST.mref (G.erased t) t_rel = HST.ralloc HS.root (G.hide Uninitialized)


let local_state = (| t, t_rel,  local_state_ref |)


let uds_is_uninitialized h =
  G.reveal (HS.sel h local_state_ref) == Uninitialized


let uds_is_initialized_predicate : HST.mem_predicate =
  fun h ->
  let x = G.reveal (HS.sel h local_state_ref) in
  x == Enabled \/ x == Disabled


let uds_is_initialized = HST.token_p local_state_ref uds_is_initialized_predicate


let uds_is_disabled_predicate : HST.mem_predicate =
  fun h -> G.reveal (HS.sel h local_state_ref) == Disabled


let uds_is_disabled = HST.token_p local_state_ref uds_is_disabled_predicate


noeq
type state = {
  uds : B.buffer uint8;
  cdi : B.buffer uint8;
  riot_header : riot_header_t;
  uds_val : s:G.erased (Seq.seq uint8){
    B.length uds == v uds_len /\
    B.length cdi == v cdi_len /\
    Seq.length (G.reveal s) == v uds_len /\
    B.freeable uds /\
    B.freeable cdi /\
    B.all_disjoint ([
      B.loc_buffer uds;
      B.loc_buffer cdi;
      B.loc_mreference local_state_ref;
      B.loc_buffer riot_header.header_sig;
      B.loc_buffer riot_header.binary;
      B.loc_buffer riot_header.pubkey])
  };
}


let get_uds st = st.uds
let get_cdi st = st.cdi
let get_uds_value st = G.reveal st.uds_val
let get_riot_header st = st.riot_header

let initialize () =
  HST.recall local_state_ref;
  HST.(local_state_ref := Enabled);
  HST.witness_p local_state_ref uds_is_initialized_predicate;

  let uds = B.malloc HS.root (u8 0x00) uds_len in
  let cdi = B.malloc HS.root (u8 0x00) cdi_len in

  let binary_size = 1ul in
  let header_sig = B.malloc HS.root (u8 0x00) 64ul in
  let binary = B.malloc HS.root (u8 0x00) 1ul in
  let pubkey = B.malloc HS.root (u8 0x00) 32ul in

  let riot_header = {
    binary_size = binary_size;
    header_sig = header_sig;
    binary = binary;
    pubkey = pubkey
  } in

  let uds_seq =
    let h = HST.get () in
    G.hide (B.as_seq h uds) in

  { uds = uds;
    cdi = cdi;
    riot_header = riot_header;
    uds_val = uds_seq }

let unset_uds st =
  let uds = get_uds st in
  B.fill uds (u8 0x00) uds_len;
  let h = HST.get () in
  assert (Seq.equal (B.as_seq h uds) (Seq.create (v uds_len) (u8 0x00)))

let disable_uds st =
  HST.recall_p local_state_ref uds_is_initialized_predicate;
  HST.(local_state_ref := Disabled);
  HST.witness_p local_state_ref uds_is_disabled_predicate;

  B.free st.uds
