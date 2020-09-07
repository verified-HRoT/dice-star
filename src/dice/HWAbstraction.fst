module HWAbstraction

module G = FStar.Ghost

module HS = FStar.HyperStack

open FStar.HyperStack.ST

module B = LowStar.Buffer
module IB = LowStar.ImmutableBuffer

module I = Lib.IntTypes

open FStar.Integers

open DICE.Definitions

type erased_pub_bytes (len:nat) = s:G.erased bytes_pub{
  Seq.length (G.reveal s) == len
}

type erased_sec_bytes (len:nat) = s:G.erased bytes_sec{
  Seq.length (G.reveal s) == len
}

val uds_len : hashable_len
let uds_len = 1ul

val uds_bytes : erased_sec_bytes (v uds_len)
let uds_bytes = G.hide (Seq.create (v uds_len) (I.u8 0))

let pub_zero = I.uint #I.U8 #I.PUB 0

val l0_image_header_size : signable_len
let l0_image_header_size = 1ul

val l0_image_header_bytes : erased_pub_bytes (v l0_image_header_size)
let l0_image_header_bytes = G.hide (Seq.create (v l0_image_header_size) pub_zero)

val l0_image_header_sig_bytes : erased_pub_bytes 64
let l0_image_header_sig_bytes = G.hide (Seq.create 64 pub_zero)

val l0_image_size : hashable_len
let l0_image_size = 1ul

val l0_image_bytes : erased_pub_bytes (v l0_image_size)
let l0_image_bytes = G.hide (Seq.create (v l0_image_size) pub_zero)

val l0_image_hash_bytes : erased_pub_bytes (v digest_len)
let l0_image_hash_bytes = G.hide (Seq.create (v digest_len) pub_zero)

val l0_auth_pubkey_bytes : erased_pub_bytes 32
let l0_auth_pubkey_bytes = G.hide (Seq.create 32 pub_zero)

type ibuffer_pub (len:nat) (s:erased_pub_bytes len) =
  b:IB.ibuffer byte_pub{IB.recallable b /\ B.length b == len /\ IB.value_is b s}

type ibuffer_sec (len:nat) (s:erased_sec_bytes len) =
  b:IB.ibuffer byte_sec{IB.recallable b /\ B.length b == len /\ IB.value_is b s}

noeq
type l0_image_t = {
  l0_image_header     : ibuffer_pub (v l0_image_header_size) l0_image_header_bytes;
  l0_image_header_sig : ibuffer_pub 64 l0_image_header_sig_bytes;

  l0_image            : ibuffer_pub (v l0_image_size) l0_image_bytes;
  l0_image_hash       : ibuffer_pub (v digest_len) l0_image_hash_bytes;

  l0_auth_pubkey      : ibuffer_pub 32 l0_auth_pubkey_bytes;
}


//not in the interface
let l0_image : l0_image_t =
  let l0_image_header = IB.igcmalloc HS.root pub_zero l0_image_header_size in
  IB.witness_value l0_image_header;
  let l0_image_header_sig = IB.igcmalloc HS.root pub_zero 64ul in
  IB.witness_value l0_image_header_sig;
  let l0_image = IB.igcmalloc HS.root pub_zero l0_image_size in
  IB.witness_value l0_image;
  let l0_image_hash = IB.igcmalloc HS.root pub_zero digest_len in
  IB.witness_value l0_image_hash;
  let l0_auth_pubkey = IB.igcmalloc HS.root pub_zero 32ul in
  IB.witness_value l0_auth_pubkey;
  { l0_image_header = l0_image_header;
    l0_image_header_sig = l0_image_header_sig;
    l0_image = l0_image;
    l0_image_hash = l0_image_hash;
    l0_auth_pubkey = l0_auth_pubkey }


val get_l0_image (_:unit) : l0_image_t
let get_l0_image _ = l0_image

let uds : b:ibuffer_sec (v uds_len) uds_bytes{B.frameOf b == HS.root} =
  let uds = IB.igcmalloc HS.root (I.u8 0) uds_len in
  IB.witness_value uds;
  uds

noeq
type state = {
  uds_enabled  : B.pointer bool;
  stack_erased : B.pointer bool;
  cdi : b:B.lbuffer byte_sec (v digest_len){
    B.frameOf uds_enabled == HS.root /\
    B.frameOf stack_erased == HS.root /\
    B.frameOf b == HS.root /\
    B.recallable uds_enabled /\
    B.recallable stack_erased /\
    B.recallable b /\
    B.(all_disjoint [loc_buffer uds_enabled; loc_buffer stack_erased; loc_buffer b])
  }
}

let st : state =
  let uds_enabled = B.gcmalloc HS.root true 1ul in
  let stack_erased = B.gcmalloc HS.root false 1ul in
  let cdi = B.gcmalloc HS.root (I.u8 0) digest_len in
  { uds_enabled = uds_enabled;
    stack_erased = stack_erased;
    cdi = cdi }


val uds_is_enabled (h:HS.mem) : Type0
let uds_is_enabled h = b2t (B.get h st.uds_enabled 0)

val stack_is_erased (h:HS.mem) : Type0
let stack_is_erased h = b2t (B.get h st.stack_erased 0)

val get_cdi_spec (_:unit) : B.lbuffer byte_sec (v digest_len)
let get_cdi_spec () = st.cdi

val get_cdi (_:unit)
  : Stack (B.lbuffer byte_sec (v digest_len))
      (requires fun h -> True)
      (ensures fun h0 b h1 ->
        h0 == h1 /\
        b == get_cdi_spec () /\
        B.live h1 b)
let get_cdi () =
  B.recall st.cdi;
  st.cdi

val read_uds (uds_out:B.lbuffer byte_sec (v uds_len))
  : Stack unit
      (requires fun h ->
        uds_is_enabled h /\
        B.live h uds_out /\
        HS.is_stack_region (B.frameOf uds_out))
      (ensures fun h0 _ h1 ->
        B.(modifies (loc_buffer uds_out) h0 h1) /\
        B.as_seq h1 uds_out == G.reveal uds_bytes /\
        uds_is_enabled h1 /\
        B.as_seq h1 (get_cdi_spec ()) == B.as_seq h0 (get_cdi_spec ()))
let read_uds uds_out =
  B.recall uds;
  IB.recall_value uds uds_bytes;
  B.recall st.uds_enabled;
  B.recall st.cdi;
  B.blit uds 0ul uds_out 0ul uds_len

val disable_uds (_:unit)
  : Stack unit
      (requires fun h -> uds_is_enabled h)
      (ensures fun h0 _ h1 ->
        (~ (uds_is_enabled h1)) /\
        B.as_seq h1 (get_cdi_spec ()) == B.as_seq h0 (get_cdi_spec ()))
let disable_uds () =
  B.recall st.uds_enabled;
  B.recall st.cdi;
  B.upd st.uds_enabled 0ul false

val platform_zeroize_stack (_:unit)
  : Stack unit
      (requires fun h -> ~ (uds_is_enabled h))
      (ensures fun h0 _ h1 ->
        (~ (uds_is_enabled h1)) /\
        stack_is_erased h1 /\
        B.as_seq h1 (get_cdi_spec ()) == B.as_seq h0 (get_cdi_spec ()))
let platform_zeroize_stack () =
  B.recall st.uds_enabled;
  B.recall st.stack_erased;
  B.recall st.cdi;
  B.upd st.stack_erased 0ul true




// let uds_len = 0x20ul
// let uds_value = fun _ -> Seq.create (v uds_len) (u8 0)
// let uds_buf = IB.igcmalloc HS.root (u8 0) uds_len

// let riot_pubkey_value = fun _ -> Seq.create 32 (u8 0)
// let riot_pubkey_buf = IB.igcmalloc HS.root (u8 0) 32ul

// let image_size = 1ul
// let riot_image_value = fun _ -> Seq.create (v image_size) (u8 0)
// let riot_image_buf = IB.igcmalloc HS.root (u8 0) image_size

// let riot_image_hash_value = fun _ -> Seq.create 32 (u8 0)
// let riot_image_hash_buf = IB.igcmalloc HS.root (u8 0) 32ul

// let header_size = 100ul
// let riot_image_header_value = fun _ -> Seq.create (v header_size) (u8 0)
// let riot_image_header_buf = IB.igcmalloc HS.root (u8 0) header_size

// let riot_header_sig_value = fun _ -> Seq.create 64 (u8 0)
// let riot_header_sig_buf = IB.igcmalloc HS.root (u8 0) 64ul

// #set-options "--__temp_no_proj HWAbstraction"

// let stack_is_zeroized h =
//   G.reveal (HS.sel h hwi_state) == Zeroized

// let uds_is_disabled h =
//   G.reveal (HS.sel h hwi_state) == Disabled

// let get_riot_image () buf_disj
// = (* Prf *) HST.recall hwi_state; (* Recall for disjointness *)
//   let pubkey = B.alloca (u8 0x00) 32ul in
//   // (* Prf *) let h = HST.get () in
//   // (* Prf *) IB.recall riot_pubkey_buf;
//   // (* Prf *) IB.recall_contents riot_pubkey_buf (Seq.create 32 (u8 0));
//   // (* Prf *) IB.buffer_immutable_buffer_disjoint pubkey riot_pubkey_buf h;
//   // B.blit riot_pubkey_buf 0ul pubkey 0ul 32ul;
//   let image_base = B.alloca (u8 0x00) image_size in
//   let image_hash = B.alloca (u8 0x00) 32ul in
//   let image_header = B.alloca (u8 0x00) header_size in
//   let header_sig = B.alloca (u8 0x00) 64ul in
//   { header_size = header_size;
//     image_header = image_header;
//     image_hash = image_hash;
//     header_sig = header_sig;
//     image_size = image_size;
//     image_base = image_base;
//     pubkey = pubkey }

// #push-options "--z3rlimit 16 --fuel 0 --ifuel 0"
// let read_uds uds
// = HST.recall hwi_state;
//   HST.(hwi_state := Copied);
//   B.fill uds (u8 0x00) uds_len
// #pop-options

// let platform_zeroize_stack ()
// = HST.recall hwi_state;
//   HST.(hwi_state := Zeroized)

// let disable_uds ()
// = HST.recall hwi_state;
//   HST.(hwi_state := Disabled)
//   // HST.witness_p local_state_ref uds_is_copied_predicate

// let platform_zeroize len b
// = B.fill b (u8 0) len;
//   let h1 = HST.get () in
//   Seq.lemma_split (B.as_seq h1 b) (v len)


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
