module HWAbstraction

/// A model of the hardware interface to be used by the DICE core
///
/// The model should be able to support following scenarios:
///   - when the addresses of UDS and CDI are some fixed addresses in Flash/SRAM/...
///     OR
///   - when a helper initializer code allocates these as buffers
///
///   - when the UDS is provisioned in the hardware already (and this layer just reads it)
///     OR
///   - when a helper initializer code provisions UDS itself (e.g. sampling some randomness)
///
/// The file HWIface.fst provides an implementation of this interface
///   to make sure that the following model is realizable
///
/// The implementation (a) allocates UDS and CDI as new buffers and (b) initialized UDS itself
///
/// For concretely running this code, we will provide a hand-written C-implementation of it
///   which will be hardware specific

open Lib.IntTypes

module P = FStar.Preorder
module G = FStar.Ghost

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

module B = LowStar.Buffer

module S = Spec.Hash.Definitions
module H = Hacl.Hash.Definitions

open DICE.Definitions

#set-options "--__temp_no_proj HWAbstraction"

val uds_len : hashable_len
val uds_value (_: unit): G.erased (lbytes_sec (v uds_len))

(* ZT: Ghost values for specifications *)
val riot_pubkey_value       (_: unit): G.erased (lbytes_sec 32)
val riot_image_value        (_: unit): G.erased (image: bytes_sec {0 < Seq.length image /\ Seq.length image <= S.max_input_length alg})
val riot_image_hash_value   (_: unit): G.erased (lbytes_sec 32)
val riot_image_header_value (_: unit): G.erased (image_header: bytes_sec {Seq.length image_header + 64<= max_size_t})
val riot_header_sig_value   (_: unit): G.erased (lbytes_sec 64)

noextract type hwi_state_t = | Enabled | Copied | Zeroized | Disabled
noextract let hwi_state_rel: P.preorder (G.erased hwi_state_t) =
  fun x1 x2 ->
  match (G.reveal x1, G.reveal x2) with
  | Enabled, Enabled | Enabled, Copied | Copied, Copied
  | Enabled, Disabled| Copied, Disabled| Disabled, Disabled
  | _, Zeroized -> True
  | _, _ -> False

  // | Enabled , Enabled  -> True
  // | _       , Enabled  -> False
  // | Copied  , Copied
  // | Enabled , Copied   -> True
  // | _       , Copied   -> False
  // | Zeroized, Zeroized
  // | Enabled , Zeroized
  // | Copied  , Zeroized -> True
  // | _       , Zeroized -> False
  // | _       , Disabled -> True

noextract let hwi_state: HST.mref (G.erased hwi_state_t) hwi_state_rel = HST.ralloc HS.root (G.hide Enabled)

(* Exposed for tracking *)
noextract let uds_is_enabled h = G.reveal (HS.sel h hwi_state) == Enabled
noextract let uds_is_copied  h = G.reveal (HS.sel h hwi_state) == Copied

(* Hided for control *)
(* ZT: `stack_is_zeroized` predicate is bound to a memory state
        and the `disable_uds` function defined later requires a
        memory state satisfies `stack_is_zeroied`, thus any buffer
        allocation and modification are forbidded.
   FIXME: Writing to immutable local variables is _not_ forbidded. *)
noextract val stack_is_zeroized (h: HS.mem): Type0
(* ZT: Although all UDS copies are zeroized and its access is disabled,
       `uds_is_disabled` is still bound to a memory state to prevent
       copying of CDI. *)
noextract val uds_is_disabled (h: HS.mem): Type0

let image_equals_to_value
  (image: image_t)
  (h: HS.mem)
= B.as_seq h image.image_base == G.reveal (riot_image_value ()) /\
  B.as_seq h image.image_hash == G.reveal (riot_image_hash_value ()) /\
  B.as_seq h image.image_header == G.reveal (riot_image_header_value ()) /\
  B.as_seq h image.header_sig == G.reveal (riot_header_sig_value ()) /\
  B.as_seq h image.pubkey == G.reveal (riot_pubkey_value ())

val get_riot_image
  (_: unit)
  (buf_disj: G.erased (B.buffer byte_sec)) (* Ideally we want to pass a (list of) loc(s), but seems we cannot say they are already allocated. *)
: HST.Stack (image_t)
  (requires fun h -> B.live h buf_disj /\ B.loc_disjoint (B.loc_buffer buf_disj) (B.loc_mreference hwi_state))
  (ensures fun h0 image h1 ->
    (* post: liveness for image *)
    h1 `contains_image` image /\ B.live h1 buf_disj /\
    (* post: tie `image` to ghost values *)
    image_equals_to_value image h1 /\
    (* post: disjointness with given locs *)
    B.all_disjoint [B.loc_buffer image.pubkey;
                    B.loc_buffer image.header_sig;
                    B.loc_buffer image.image_header;
                    B.loc_buffer image.image_hash;
                    B.loc_buffer image.image_base;
                    G.reveal (B.loc_buffer buf_disj);
                    B.loc_mreference hwi_state] /\
    B.modifies (B.loc_none) h0 h1)

val read_uds
  (uds: B.lbuffer byte_sec (v uds_len))
: HST.Stack unit
  (requires fun h ->
    (* pre: in state `initialized` *)
    uds_is_enabled h /\
    (* pre: image is valid *)
    is_valid_image (G.reveal (riot_pubkey_value ()))
                   (G.reveal (riot_image_value ()))
                   (G.reveal (riot_image_hash_value ()))
                   (G.reveal (riot_image_header_value ()))
                   (G.reveal (riot_header_sig_value ())) /\
    B.live h uds /\ B.loc_disjoint (B.loc_buffer uds) (B.loc_mreference hwi_state))
  (ensures fun h0 _ h1 ->
    uds_is_copied h1 /\
    h1 `HS.contains` hwi_state /\
    B.live h1 uds /\
    (* post: only `uds` and ref is modified *)
    B.modifies (B.loc_buffer uds `B.loc_union` B.loc_mreference hwi_state) h0 h1 /\
    (* post: tie `uds` to ghost value *)
    B.as_seq h1 uds == G.reveal (uds_value ()))

val platform_zeroize_stack (_: unit)
: HST.Stack unit
  (requires fun h ->
    (* pre: image is valid and secrets are zeroized *)
    uds_is_copied h)
  (ensures fun h0 _ h1 ->
    stack_is_zeroized h1 /\
    h1 `HS.contains` hwi_state /\
    (* NOTE: Since `hwi_state` is modified, no predicates other than the opaque
             `stack_is_zeroized` holds. *)
    (* FIXME: Not sure if we should be more precise about this modifies clause,
              since all buffers on stack are meant to be zeroized *)
    B.(modifies (loc_mreference hwi_state) h0 h1))

val disable_uds (_: unit)
: HST.Stack unit
  (requires fun h ->
   (* pre: image is valid and secrets are zeroized *)
    stack_is_zeroized h \/
   (* pre: OR image is invalid and secrets were never copied *)
   (uds_is_enabled h /\
    ~ (is_valid_image (G.reveal (riot_pubkey_value ()))
                      (G.reveal (riot_image_value ()))
                      (G.reveal (riot_image_hash_value ()))
                      (G.reveal (riot_image_header_value ()))
                      (G.reveal (riot_header_sig_value ())))))
  (ensures fun h0 _ h1 ->
    uds_is_disabled h1 /\
    h1 `HS.contains` hwi_state /\
    (* NOTE: Since `hwi_state` is modified, no predicates other than the opaque
             `uds_is_disabled` holds. *)
    B.(modifies (loc_mreference hwi_state) h0 h1))

(* Just (defensively) zeroize a buffer, we may not actually use it *)
val platform_zeroize
  (len: size_t)
  (b: B.lbuffer byte_sec (v len))
: HST.Stack unit
  (requires fun h -> B.live h b)
  (ensures fun h0 _ h1 ->
    B.modifies (B.loc_buffer b) h0 h1 /\
    B.as_seq h1 b == Seq.create (v len) (u8 0x00))
