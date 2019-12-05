/// Reference: https://github.com/microsoft/RIoT/blob/master/Reference/DICE/DiceCore.cpp
module Minimal.DICE

open LowStar.BufferOps
(* since there will be confusions about `cast` in both modules, I closed them for now *)
// open Lib.IntTypes
// open FStar.Integers

open Spec.Hash.Definitions
open Hacl.Hash.Definitions

open Lib.IntTypes

open HWIface

module I  = FStar.Integers
module HI  = Lib.IntTypes

module SHA2       = Hacl.Hash.SHA2
module SHA1       = Hacl.Hash.SHA1
module MD5        = Hacl.Hash.MD5
module HMAC       = Hacl.HMAC
module Ed25519    = Hacl.Ed25519
// module Curve25519 = Hacl.Curve25519

(* NOTE: Hash and HMAC are using LowStar.Buffer, while Ed25519 is using Lib.Buffer *)
module B   = LowStar.Buffer
module LB  = Lib.Buffer
module M   = LowStar.Modifies
module HS  = FStar.HyperStack
module HST = FStar.HyperStack.ST
module IB  = LowStar.ImmutableBuffer
// module Seq = Lib.Sequence

/// <><><><><><><><><><><><> RIoT Loader Interface <><><><><><><><><><><><><>
let version_number_t = pub_uint32
(* NOTE: `Hacl.Ed25519` uses their own `Lib.Sequence`, `Lib.Buffer`, etc., but `Hacl.Hash.*` doesn't *)
let signature_t = LB.lbuffer uint8 64ul
let publickey_t = LB.lbuffer uint8 32ul
let secretkey_t = LB.lbuffer uint8 32ul
let msg_len_t = a:size_t{v a + 64 <= max_size_t}
assume val riot_header_len: a:size_t{0 < v a /\ v a <= max_input_length SHA2_512}
let raw_rheader_t = LB.lbuffer uint8 riot_header_len

(* EXTENDED riot header
   prefix `rh` for "RIoT Header" and
   prefix `rb` for "RIoT Binary" *)
noeq
type riot_exheader_t = {
     (* actual entries in headers*)
     rversion  : version_number_t;
     rbsize    : riot_size_t;
     rbhash    : digest_t;
     rhsig     : signature_t;
     (* extra entries for convenience *)
     rhraw     : raw_rheader_t
  }

noeq
type riot_t = {
  rsize   : riot_size_t;
  rbinary : b:B.buffer uint8{B.length b == v rsize \/ b == B.null}
  }

let rcontains (h:HS.mem) (rheader: riot_exheader_t) =
  B.live h rheader.rbhash /\
  LB.live h rheader.rhsig /\
  LB.live h rheader.rhraw

let get_rheader_loc_l rheader = [B.loc_buffer rheader.rbhash
                                ;LB.loc rheader.rhsig
                                ;LB.loc rheader.rhraw]

let load_rheader (_:unit)
  (* NOTE: allocate on caller's stack *)
: HST.StackInline (rheader: riot_exheader_t)
  (requires fun h ->
    (* FIXME: maintain disjointness is troublesome since I allocated different
              buffers in different functions.
              I didn't pass other buffers in and maintain disjointness for now.
              I'll come back and find a better way. *)
    True)
  (ensures fun h0 rheader h1 ->
    B.modifies B.loc_none h0 h1 /\
    h1 `rcontains` rheader /\
    B.all_disjoint (get_rheader_loc_l rheader))
=
  let rversion = uint #U32 #PUB 1 in
  let rbsize   = 100ul in
  let rbhash   = B.alloca (u8 0x00) digest_len in
  let rhsig    = LB.create 64ul (u8 0x00) in
  let rhraw    = LB.create riot_header_len (u8 0x00) in
  {rversion = rversion; rbsize = rbsize; rbhash = rbhash; rhsig = rhsig; rhraw = rhraw}

let verify_header
  (rheader: riot_exheader_t)
  (rhpubkey: publickey_t)
: HST.StackInline bool
  (requires fun h ->
    h `rcontains` rheader /\
    LB.live h rhpubkey
    (* FIXME: maintain disjointness is troublesome since I allocated different buffers in different functions.
              I just forget it for now. I'll come back and find a better way. *)
    // B.all_disjoint ((get_rheader_loc_l rheader)@[LB.loc rhpubkey])
    )
  (ensures  fun h0 b h1 -> True)
    (* FIXME: I haven't find the compatible SHA2 512 hash spec for Ed25519,
              since hash uses Seq and Ed25519 uses Lib.Sequence in HALC*.
              I believe there is a way and I will fix this tomorrow *)
    // let rheader_hash = Spec.Agile.Hash.hash alg (LB.as_seq h0 rheader.rhraw) in
    // b == Spec.Ed25519.verify (LB.as_seq h0 rhpubkey) rheader_hash (LB.as_seq h0 rheader.rhsig))
=
  let rheader_hash = LB.create 64ul (u8 0x00) in
  SHA2.hash_512_lib riot_header_len rheader.rhraw rheader_hash;
  Ed25519.verify rhpubkey 64ul rheader_hash rheader.rhsig

(* Duties:
   1. load RIoT header
   2. authenticate RIoT header
   3. load RIoT binary *)
let load_riot
  (rhpubkey: publickey_t)
: HST.StackInline (riot: riot_t)
  (requires fun h ->
    LB.live h rhpubkey)
  (ensures  fun h0 riot h1 ->
    B.live h1 riot.rbinary)
=
  let rheader = load_rheader () in
  if (verify_header rheader rhpubkey)
  then (* succeed *)
    {rsize = rheader.rbsize; rbinary = B.alloca (u8 0x00) rheader.rbsize}
  else (* failed *)
    {rsize = rheader.rbsize; rbinary = B.null}

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

/// <><><><><><><><><><><><> DICE main funtion <><><><><><><><><><><>

(* This old version `dice_on_stack` is for reference purpose, not what we want finally *)
(* F* warns when set `--query_stats` *)
#reset-options "--z3rlimit 30 --query_stats"
let dice_main
  (st: state)
  (riot_size: riot_size_t)
  (riot_binary: B.buffer uint8{B.length riot_binary == v riot_size})
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
    = B.alloca (HI.u8 0x00) digest_len in
  dice_hash alg
    uds uds_len
    uDigest;

  (**)let h1 = HST.get () in
  (**)assert (B.modifies (B.loc_buffer uDigest) h0 h1 /\
  (**)        B.as_seq h1 uDigest == Spec.Agile.Hash.hash alg (B.as_seq h0 uds));

  (* compute rDigest *)
  let rDigest: b:B.buffer HI.uint8{B.length b == hash_length alg}
    = B.alloca (HI.u8 0x00) digest_len in
  dice_hash alg
    riot_binary riot_size
    rDigest;

  (**)let h2 = HST.get () in
  (**)assert (B.modifies (B.loc_buffer rDigest) h1 h2 /\
  (**)        B.as_seq h2 rDigest == Spec.Agile.Hash.hash alg (B.as_seq h1 riot_binary));

  (* compute cdi *)
  (**)assert_norm (Spec.Agile.HMAC.keysized alg (v digest_len));
  dice_hmac alg
    cdi
    uDigest digest_len
    rDigest digest_len;

  HST.pop_frame()

/// <><><><><><><><><><><><> C main funtion <><><><><><><><><><><>

assume val riot_size: riot_size_t

assume val riot_binary:
  b:B.buffer uint8
    {B.length b == v riot_size /\
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
