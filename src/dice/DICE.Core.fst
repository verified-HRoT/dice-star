/// Reference: https://github.com/microsoft/RIoT/blob/master/Reference/DICE/DiceCore.cpp

module DICE.Core

open LowStar.Comment

module Fail = LowStar.Failure
module B = LowStar.Buffer
module HS  = FStar.HyperStack
module HST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.ByteBuffer
module S = Spec.Hash.Definitions
module Ed25519 = Hacl.Ed25519

module HW = HWAbstraction

open DICE.Definitions

#set-options "--z3rlimit 20"

let authenticate_image
  (image: image_t)
: HST.Stack bool
 (requires fun h ->
   h `contains_image` image)
 (ensures fun h0 result h1 ->
   B.modifies B.loc_none h0 h1 /\
   h1 `contains_image` image /\
  (result <==> is_valid_image_st image h0))
= HST.push_frame ();
  let valid_header_sig = Ed25519.verify
                         (* pub *) image.pubkey
                         (* msg *) image.header_size image.image_header
                         (* sig *) image.header_sig in
  if (valid_header_sig) then
  ( let computed_image_hash = B.alloca (u8 0x00) digest_len in
    let image_binary = B.sub image.image_base 0ul image.image_size in
    let valid_image_hash = dice_hash alg
                           (* msg *) image_binary image.image_size
                           (* dst *) computed_image_hash in
    let valid_image = lbytes_eq #digest_len image.image_hash computed_image_hash in
    HST.pop_frame();
(* return *) valid_image )
  else
  ( HST.pop_frame ();
(* return *) false )

let lemma_hmac_preconditions ()
: Lemma
  (Spec.Agile.HMAC.keysized alg (v digest_len) /\
   v digest_len + S.block_length alg <= S.max_input_length alg)
= assert_norm (Spec.Agile.HMAC.keysized alg (v digest_len) /\
               v digest_len + S.block_length alg <= S.max_input_length alg)

module G = FStar.Ghost

let derive_cdi_spec
  (uds : lbytes_sec (v HW.uds_len) { uds == G.reveal (HW.uds_value ()) })
  (riot: bytes_sec { //Seq.length riot <= Spec.Hash.Definitions.max_input_length alg /\
                     riot == G.reveal (HW.riot_image_value())})
: GTot (lbytes_sec (v digest_len))
= (* Prf *) lemma_hmac_preconditions ();
  Spec.Agile.HMAC.hmac alg
    (Spec.Agile.Hash.hash alg uds)
    (Spec.Agile.Hash.hash alg riot)

let derive_cdi
  (uds: B.lbuffer byte_sec (v HW.uds_len))
  (riot_size: hashable_len)
  (riot: B.lbuffer byte_sec (v riot_size))
  (cdi: B.lbuffer byte_sec (v digest_len))
: HST.Stack unit
  (requires fun h ->
    B.live h uds /\ B.live h riot /\ B.live h cdi /\
    B.all_disjoint [B.loc_buffer uds; B.loc_buffer riot; B.loc_buffer cdi] /\
    B.as_seq h uds == G.reveal (HW.uds_value ()) /\
    B.as_seq h riot == G.reveal (HW.riot_image_value ()))
  (ensures fun h0 _ h1 ->
    B.modifies (B.loc_buffer cdi) h0 h1 /\
    B.as_seq h1 cdi == derive_cdi_spec (B.as_seq h0 uds) (B.as_seq h0 riot))
= HST.push_frame ();
  let uds_digest  = B.alloca (u8 0x00) digest_len in
  let riot_digest = B.alloca (u8 0x00) digest_len in
  dice_hash alg uds HW.uds_len uds_digest;
  dice_hash alg riot riot_size riot_digest;
  (* Prf *) lemma_hmac_preconditions ();
  dice_hmac alg
    (* dst *) cdi
    (* key *) uds_digest  digest_len
    (* msg *) riot_digest digest_len;
  HST.pop_frame ()

let dice_core
  (cdi: B.lbuffer byte_sec (v digest_len))
  (image: image_t)
: HST.Stack unit
  (requires fun h ->
    h `contains_image` image /\ B.live h cdi /\
    HW.uds_is_enabled h /\
    B.all_disjoint [B.loc_buffer cdi;
                    B.loc_buffer image.pubkey;
                    B.loc_buffer image.header_sig;
                    B.loc_buffer image.image_header;
                    B.loc_buffer image.image_hash;
                    B.loc_buffer image.image_base;
                    B.loc_mreference HW.hwi_state] /\
    HW.image_equals_to_value image h /\
    is_valid_image_st image h)
  (ensures fun h0 _ h1 ->
    B.modifies (B.loc_buffer cdi `B.loc_union` B.loc_mreference HW.hwi_state) h0 h1 /\
    HW.uds_is_copied h1 /\
    B.as_seq h1 cdi == derive_cdi_spec
                       (G.reveal (HW.uds_value ()))
                       (G.reveal (HW.riot_image_value ())))
= (* Prf *) HST.recall HW.hwi_state; (* for disjointness *)
  HST.push_frame ();

(* Copy UDS to a memory on stack *)
  let uds = B.alloca (u8 0x00) HW.uds_len in
  HW.read_uds uds;

(* Derive CDI *)
  derive_cdi
    (* uds *) uds
    (* img *) image.image_size image.image_base
    (* cdi *) cdi;

  HST.pop_frame ()

type dice_return_code =
| DICE_SUCCESS | DICE_ERROR

let f ()
: HST.Unsafe unit
  (requires fun h -> HW.uds_is_copied h)
  (ensures fun h0 _ h1 -> True)
= HW.platform_zeroize_stack ();
  HW.disable_uds ()

#push-options "--query_stats --z3rlimit 256 --fuel 0 --ifuel 0"
let dice_main
  (cdi: B.lbuffer byte_sec (v digest_len))
: HST.Stack dice_return_code
  (requires fun h ->
    HW.uds_is_enabled h /\
    B.live h cdi /\ B.loc_disjoint (B.loc_buffer cdi) (B.loc_mreference HW.hwi_state))
  (ensures fun h0 code h1 -> True /\
    // h1 `HS.contains` HW.hwi_state /\
    HW.uds_is_disabled h1 /\
    (code == DICE_SUCCESS ==> is_valid_image (G.reveal (HW.riot_pubkey_value ()))
                                                (G.reveal (HW.riot_image_value ()))
                                                (G.reveal (HW.riot_image_hash_value ()))
                                                (G.reveal (HW.riot_image_header_value ()))
                                                (G.reveal (HW.riot_header_sig_value ())) /\
                                                B.as_seq h1 cdi == derive_cdi_spec
                                                                     (G.reveal (HW.uds_value ()))
                                                                     (G.reveal (HW.riot_image_value ())) ) /\
       (code == DICE_ERROR ==> ~ (is_valid_image (G.reveal (HW.riot_pubkey_value ()))
                                                (G.reveal (HW.riot_image_value ()))
                                                (G.reveal (HW.riot_image_hash_value ()))
                                                (G.reveal (HW.riot_image_header_value ()))
                                                (G.reveal (HW.riot_header_sig_value ())))) /\
    True
    )
= (* Prf *) HST.recall HW.hwi_state; (* for liveness *)

  let image = HW.get_riot_image () (G.hide cdi) in
  let valid_image = authenticate_image image in

  if (not valid_image) then
  (
(* Disable UDS and exit *)
   (* FIXME: For some reason the pre and post condition of `HW.disable_uds`
             and `HW.platform_zeroize_stack` is not working*)
    HW.disable_uds ();
    DICE_ERROR )
  else
  (
(* Derive CDI *)
    dice_core cdi image;

(* Zeroize Stack *)
    HW.platform_zeroize_stack ();

(* Disable UDS and exit *)
    HW.disable_uds ();
    DICE_SUCCESS )
