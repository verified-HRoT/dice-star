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
let header_len = 0x20ul
let entry_t = unit -> HST.St unit
let entry = fun () -> ()

noeq
type header_t = {
     (* actual entries in headers*)
     binary_size   : binary_size_t;
     binary_hash   : digest_t;
     header_sig    : signature_t;
     (* extra entries for convenience *)
     binary        : B.lbuffer uint8 (v binary_size);
     header_raw    : header_raw_t;
     header_pubkey : publickey_t;
     entry         : entry_t;
     header_inv    : u:unit{
       B.(all_disjoint [ loc_buffer binary_hash
                       ; loc_buffer header_sig
                       ; loc_buffer binary
                       ; loc_buffer header_raw
                       ; loc_buffer header_pubkey
       ])
     }
}

let get_binary_size header = header.binary_size
let get_binary_hash header = header.binary_hash
let get_header_sig  header = header.header_sig
let get_binary      header = header.binary
let get_header_raw  header = header.header_raw
let get_header_pubkey header = header.header_pubkey
let get_entry       header = header.entry

/// <><><><><><><><><><><><> Monotonic Predicates <><><><><><><><><><><><>
/// 
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

/// <><><><><><><><><><><><><><><><> State <><><><><><><><><><><><><><><><>

noeq
type state = {
  uds     : B.buffer uint8;
  cdi     : B.buffer uint8;
  header  : header_t;
  uds_val : s:G.erased (Seq.seq uint8){
    B.length uds == v uds_len /\
    B.length cdi == v cdi_len /\
    Seq.length (G.reveal s) == v uds_len /\
    B.freeable uds /\
    B.freeable cdi /\
    B.all_disjoint ([B.loc_buffer uds
                   ; B.loc_buffer cdi
                   ; B.loc_mreference local_state_ref] @
                   (get_header_loc_l header))
  }
}

let get_uds st = st.uds
let get_cdi st = st.cdi
let get_header st = st.header
let get_uds_value st = G.reveal st.uds_val

let load_header
  (_: unit)
: HST.ST (header: header_t)
  (requires fun h -> True)
  (ensures fun h0 header h1 -> True)
=
  let binary_size:binary_size_t   = 100ul in
  let binary_hash   = B.malloc HS.root (u8 0x00) digest_len in
  let header_sig    = B.malloc HS.root (u8 0x00) 64ul in
  let binary        = B.malloc HS.root (u8 0x00) binary_size in
  let header_raw    = B.malloc HS.root (u8 0x00) header_len in
  let header_pubkey = B.malloc HS.root (u8 0x00) 32ul in
  { binary_size = binary_size
  ; binary_hash = binary_hash
  ; header_sig  = header_sig
  ; binary      = binary
  ; header_raw  = header_raw
  ; header_pubkey = header_pubkey
  ; entry       = entry
  ; header_inv  = () }

#reset-options "--z3rlimit 50"
#push-options "--query_stats"
let initialize () =
  HST.recall local_state_ref;
  HST.(local_state_ref := Enabled);
  HST.witness_p local_state_ref uds_is_initialized_predicate;

  let uds = B.malloc HS.root (u8 0x00) uds_len in
  let cdi = B.malloc HS.root (u8 0x00) uds_len in
  let binary_size   = 100ul in
  let binary_hash   = B.malloc HS.root (u8 0x00) digest_len in
  let header_sig    = B.malloc HS.root (u8 0x00) 64ul in
  let binary        = B.malloc HS.root (u8 0x00) binary_size in
  let header_raw    = B.malloc HS.root (u8 0x00) header_len in
  let header_pubkey = B.malloc HS.root (u8 0x00) 32ul in

  let uds_seq =
    let h = HST.get () in
    G.hide (B.as_seq h uds) in

  { uds = uds
  ; cdi = cdi
  ; header  = { binary_size = binary_size
              ; binary_hash = binary_hash
              ; header_sig  = header_sig
              ; binary      = binary
              ; header_raw  = header_raw
              ; header_pubkey = header_pubkey
              ; entry       = entry
              ; header_inv  = () }
  ; uds_val = uds_seq }

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
