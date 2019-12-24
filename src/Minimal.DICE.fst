/// Reference: https://github.com/microsoft/RIoT/blob/master/Reference/DICE/DiceCore.cpp

module Minimal.DICE

module Fail = LowStar.Failure
module B = LowStar.Buffer
module HS  = FStar.HyperStack
module HST = FStar.HyperStack.ST

open Lib.IntTypes
module S = Spec.Hash.Definitions
module Ed25519 = Hacl.Ed25519

module HW = Minimal.Hardware

open DICE.Definitions

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 20"


/// Factoring out some preconditions required to invoke hmac routines

let hmac_preconditions ()
: Lemma 
  (Spec.Agile.HMAC.keysized alg (v digest_len) /\
   v digest_len + S.block_length alg <= S.max_input_length alg)
= assert_norm (Spec.Agile.HMAC.keysized alg (v digest_len) /\
               v digest_len + S.block_length alg <= S.max_input_length alg)


/// Setting up the specifications of the DICE core functionality
///
/// The first property is that the RIoT header signature verifies

let riot_signature_verifies (riot_header:riot_header_t) (h:HS.mem) =
  let digest = Spec.Agile.Hash.hash alg (B.as_seq h riot_header.binary) in  
  Spec.Ed25519.verify (B.as_seq h riot_header.pubkey) digest (B.as_seq h riot_header.header_sig)

/// The next property says that the computed CDI is hmac of hash of the RIoT binary
///   computed with the hash of the UDS as key 

let cdi_is_hmac (state:HW.state) (h:HS.mem) =
  let cdi = HW.get_cdi state in
  let uds = HW.get_uds state in
  hmac_preconditions ();
  B.as_seq h cdi ==
    Spec.Agile.HMAC.hmac alg
      (Spec.Agile.Hash.hash alg (HW.get_uds_value state))
      (Spec.Agile.Hash.hash alg (B.as_seq h (HW.get_riot_header state).binary))


/// The postcondition in addition says that the DICE core
///   only modifies the CDI buffer

unfold let dice_core_post (state:HW.state)
: HS.mem -> unit -> HS.mem -> Type0
= fun h0 r h1 ->
  B.(modifies (loc_buffer (HW.get_cdi state)) h0 h1) /\
  riot_signature_verifies (HW.get_riot_header state) h1 /\
  cdi_is_hmac state h1


/// Preconditions (established by HW initialize)

unfold
let dice_core_pre (state:HW.state)
: HS.mem -> Type0
= fun h ->
  h `HW.contains` state /\
  HW.disjointness state /\
  B.as_seq h (HW.get_uds state) == HW.get_uds_value state


/// The DICE core functionality
///
/// It allocates two buffers on stack to compute the digests of the RIoT binary and UDS

inline_for_extraction
let dice_core_aux (state:HW.state)
: HST.StackInline unit
  (requires dice_core_pre state)
  (ensures dice_core_post state)
= let h1 = HST.get () in

  //stack allocations
  let riot_binary_digest = B.alloca (u8 0x00) digest_len in
  let uds_digest = B.alloca (u8 0x00) digest_len in

  let h2 = HST.get () in

  //verification of the RIoT binary signature
  let riot_header = HW.get_riot_header state in
  dice_hash alg riot_header.binary riot_header.binary_size riot_binary_digest;
  let b = Ed25519.verify riot_header.pubkey digest_len riot_binary_digest riot_header.header_sig in

  if not b then Fail.failwith "RIoT signature verification failed"
  else
    //CDI computation
    let uds = HW.get_uds state in
    let cdi = HW.get_cdi state in
    dice_hash alg uds HW.uds_len uds_digest;
    hmac_preconditions ();
    dice_hmac alg cdi uds_digest digest_len riot_binary_digest digest_len;

    //proof hints for `modifies` to the solver
    let h3 = HST.get () in
    B.modifies_remove_new_locs
      (B.(loc_union (loc_buffer riot_binary_digest) (loc_buffer uds_digest)))
      B.loc_none
      (B.loc_buffer cdi)
      h1 h2 h3

/// Wrapper over the dice_core_aux

let dice_core (state:HW.state)
: HST.Stack unit
  (requires dice_core_pre state)
  (ensures dice_core_post state)
= HST.push_frame ();
  dice_core_aux state;
  HST.pop_frame ()

let dice_main ()
: HST.ST unit
  (requires fun h ->
    HW.uds_is_uninitialized h)
  (ensures fun _ _ _ -> HW.uds_is_disabled)
= let state = HW.initialize () in
  dice_core state;

  HW.unset_uds state;
  HW.disable_uds state
