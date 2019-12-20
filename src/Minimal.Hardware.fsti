module Minimal.Hardware

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

open Spec.Hash.Definitions
open Hacl.Hash.Definitions

module P = FStar.Preorder
module G = FStar.Ghost

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

module B = LowStar.Buffer

/// <><><><><><><><><><><><> Common Definitions <><><><><><><><><><><><>

unfold
let dice_alg = a:hash_alg{a <> MD5 /\ a <> SHA2_224}

unfold
let alg : dice_alg = SHA2_256

unfold inline_for_extraction noextract
let dice_hash (alg: dice_alg): hash_st alg =
  match alg with
  | SHA2_256 -> Hacl.Hash.SHA2.hash_256
  | SHA2_384 -> Hacl.Hash.SHA2.hash_384
  | SHA2_512 -> Hacl.Hash.SHA2.hash_512
  | SHA1     -> Hacl.Hash.SHA1.legacy_hash

unfold inline_for_extraction noextract
let dice_hmac (alg: dice_alg): Hacl.HMAC.compute_st alg =
  match alg with
  | SHA2_256 -> Hacl.HMAC.compute_sha2_256
  | SHA2_384 -> Hacl.HMAC.compute_sha2_384
  | SHA2_512 -> Hacl.HMAC.compute_sha2_512
  | SHA1     -> Hacl.HMAC.legacy_compute_sha1

unfold
let digest_len = hash_len alg

unfold
let digest_t = hash_t alg

val uds_len : l: size_t {0 < v l /\ v l <= max_input_length alg}

unfold
let cdi_len = digest_len

let binary_size_t = a:size_t{0 < v a /\ v a <= max_input_length alg}

val header_len: binary_size_t

let signature_t = B.lbuffer uint8 64
let publickey_t = B.lbuffer uint8 32
let secretkey_t = B.lbuffer uint8 32
let msg_len_t = a:size_t{v a + 64 <= max_size_t}

let header_raw_t = B.lbuffer uint8 (v header_len)

val entry_t: Type0
val entry: entry_t

val header_t: Type0
val get_binary_size (header: header_t): binary_size_t
val get_binary_hash (header: header_t): digest_t
val get_header_sig  (header: header_t): signature_t
val get_binary      (header: header_t): B.lbuffer uint8 (v (get_binary_size header))
val get_header_raw  (header: header_t): header_raw_t
val get_header_pubkey (header: header_t): publickey_t
val get_entry       (header: header_t): entry_t

unfold noextract
let contains_header (h:HS.mem) (header: header_t) =
  B.live h (get_binary_hash header) /\
  B.live h (get_header_sig header) /\
  B.live h (get_header_raw header) /\
  B.live h (get_header_pubkey header) /\
  B.live h (get_binary header)

unfold noextract
let get_header_loc_l header = [B.loc_buffer (get_binary_hash header)
                              ;B.loc_buffer (get_header_sig header)
                              ;B.loc_buffer (get_header_raw header)
                              ;B.loc_buffer (get_header_pubkey header)
                              ;B.loc_buffer (get_binary header)]

/// <><><><><><><><><><> Monotonic Predicates <><><><><><><><><><><>

/// The model maintains some abstract local state
///
/// The state is a reference to an erased (ghost) value,
///   and so, we can be sure that it doesn't impact the concrete executions
///
/// This type can be left out of the native C implementation of this interface

noextract
val local_state : ( a:Type0 & pre:P.preorder (G.erased a) & HST.mref (G.erased a) pre)


/// Following predicates define the state machine for UDS
///
/// At the beginning uds_is_uninitialized
///   It is a stateful predicate, since when the UDS is initialized, the predicate ceases to hold
///
/// Then the UDS becomes initialized
///   And this is a PURE, state independent predicate, once initialized UDS remains so
///
/// Then at some point UDS will be disabled, again once disabled remains disabled
///
/// These are just for spec purposes, can be left out of the native implementation

val uds_is_uninitialized (h:HS.mem) : Type0

val uds_is_initialized : Type0

val uds_is_disabled : Type0


/// Now the state of the interface, again as an abstract type
///
/// The state provides getters for UDS and CDI (see below)
///   so the native implementation can implement it simply as a record of two pointers (uds and cdi)

val state : Type0

/// Clients can get the uds and the cdi buffer from the state
///   And also value of the UDS for the purposed of the spec

val get_uds (st:state)
: Tot (b:B.buffer uint8{B.length b == v uds_len /\ B.freeable b})

val get_cdi (st:state)
: Tot (b:B.buffer uint8{B.length b == v cdi_len /\ B.freeable b})

val get_header (st: state)
: Tot (h: header_t{
          B.all_disjoint (get_header_loc_l h) /\
          B.length (get_binary h) == v (get_binary_size h)})

val get_uds_value (st:state)
: GTot (s:Seq.seq uint8{Seq.length s == v uds_len})

/// Helper

unfold
let get_loc_l st = [ B.loc_buffer (get_uds st)
                   ; B.loc_buffer (get_cdi st) ] @
                   (get_header_loc_l (get_header st))

unfold
let contains (h:HS.mem) (st:state) =
  B.live h (get_uds st) /\
  B.live h (get_cdi st) /\
  h `contains_header` (get_header st)

/// <><><><><><><><><><><><><><> Interfaces <><><><><><><><><><><><><><><><><><>

/// The initialization routine
///
/// It requires a precondition that uds_is_uninitialized
///   We will add this as a precondition (assumption) to the DICE core main function
///   After this function is called, the clients cannot call it again
///   since they won't be able to prove that uds_is_uninitialized in the output memory
///
/// It provides liveness and disjointness of various state elements
///
/// It also provides as a postcondition, the fact that the value of the UDS buffer
///   is same as the value of the ghost uds (as given by the get_uds_value function)
///
/// TODO: this currently does not say anything about the allocations it does
///       e.g. this function is currently allowed to allocate two uds buffers and copy UDS into them

val initialize (_: unit)
: HST.ST (st:state{B.all_disjoint (get_loc_l st)})
  (requires fun h ->
    uds_is_uninitialized h)
  (ensures fun h0 st h1 ->
    uds_is_initialized /\  //uds has been initialized
    (let (| _, _, local_st |) = local_state in
     let uds  = get_uds st in
     HS.contains h1 local_st /\
     B.(modifies (loc_mreference local_st) h0 h1) /\
     h1 `contains` st /\
     B.all_disjoint ((get_loc_l st)
                    @[B.loc_mreference local_st]) /\
     B.as_seq h1 uds == get_uds_value st))


/// Zeroing out UDS
///
/// Also says that it doesn't perform any allocation
///   (actually it could have allocated and deallocated)

val unset_uds (st:state)
: HST.ST unit
  (requires fun h ->
    uds_is_initialized /\ h `contains` st)
  (ensures fun h0 _ h1 ->
    let uds = get_uds st in
    HST.equal_domains h0 h1 /\
    B.(modifies (loc_buffer uds) h0 h1) /\
    B.as_seq h1 uds == Seq.create (v uds_len) (u8 0x00))


/// Disable UDS
///
/// Requires that the clients must have zeroed out UDS already
///
/// Takes away the liveness of the UDS buffer
///   i.e. clients cannot read/write to it anymore

val disable_uds (st:state)
: HST.ST unit
  (requires fun h ->
    uds_is_initialized /\
    h `contains` st /\
    Seq.equal (B.as_seq h (get_uds st)) (Seq.create (v uds_len) (u8 0x00)))
  (ensures fun h0 _ h1 ->
    uds_is_disabled /\  //uds has been disabled
    (let (| _, _, local_st |) = local_state in
     let uds = get_uds st in
     B.(modifies (loc_union (loc_addr_of_buffer uds)
                            (loc_mreference local_st)) h0 h1)))
