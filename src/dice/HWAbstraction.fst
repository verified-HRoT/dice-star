module HWAbstraction

module P = FStar.Preorder
module G = FStar.Ghost

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

module B = LowStar.Buffer
module IB = LowStar.ImmutableBuffer

let uds_len = 0x20ul
let uds_value = fun _ -> Seq.create (v uds_len) (u8 0)
let uds_buf = IB.igcmalloc HS.root (u8 0) uds_len

let riot_pubkey_value = fun _ -> Seq.create 32 (u8 0)
let riot_pubkey_buf = IB.igcmalloc HS.root (u8 0) 32ul

let image_size = 1ul
let riot_image_value = fun _ -> Seq.create (v image_size) (u8 0)
let riot_image_buf = IB.igcmalloc HS.root (u8 0) image_size

let riot_image_hash_value = fun _ -> Seq.create 32 (u8 0)
let riot_image_hash_buf = IB.igcmalloc HS.root (u8 0) 32ul

let header_size = 100ul
let riot_image_header_value = fun _ -> Seq.create (v header_size) (u8 0)
let riot_image_header_buf = IB.igcmalloc HS.root (u8 0) header_size

let riot_header_sig_value = fun _ -> Seq.create 64 (u8 0)
let riot_header_sig_buf = IB.igcmalloc HS.root (u8 0) 64ul

#set-options "--__temp_no_proj HWAbstraction"

let stack_is_zeroized h =
  G.reveal (HS.sel h hwi_state) == Zeroized

let uds_is_disabled h =
  G.reveal (HS.sel h hwi_state) == Disabled

let get_riot_image () buf_disj
= (* Prf *) HST.recall hwi_state; (* Recall for disjointness *)
  let pubkey = B.alloca (u8 0x00) 32ul in
  // (* Prf *) let h = HST.get () in
  // (* Prf *) IB.recall riot_pubkey_buf;
  // (* Prf *) IB.recall_contents riot_pubkey_buf (Seq.create 32 (u8 0));
  // (* Prf *) IB.buffer_immutable_buffer_disjoint pubkey riot_pubkey_buf h;
  // B.blit riot_pubkey_buf 0ul pubkey 0ul 32ul;
  let image_base = B.alloca (u8 0x00) image_size in
  let image_hash = B.alloca (u8 0x00) 32ul in
  let image_header = B.alloca (u8 0x00) header_size in
  let header_sig = B.alloca (u8 0x00) 64ul in
  { header_size = header_size;
    image_header = image_header;
    image_hash = image_hash;
    header_sig = header_sig;
    image_size = image_size;
    image_base = image_base;
    pubkey = pubkey }

#push-options "--z3rlimit 16 --fuel 0 --ifuel 0"
let read_uds uds
= HST.recall hwi_state;
  HST.(hwi_state := Copied);
  B.fill uds (u8 0x00) uds_len
#pop-options

let platform_zeroize_stack ()
= HST.recall hwi_state;
  HST.(hwi_state := Zeroized)

let disable_uds ()
= HST.recall hwi_state;
  HST.(hwi_state := Disabled)
  // HST.witness_p local_state_ref uds_is_copied_predicate

let platform_zeroize len b
= B.fill b (u8 0) len;
  let h1 = HST.get () in
  Seq.lemma_split (B.as_seq h1 b) (v len)


(* Old implemenations
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


(* Old Implementation
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
