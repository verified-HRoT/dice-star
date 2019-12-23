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

module P = FStar.Preorder
module G = FStar.Ghost

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

module B = LowStar.Buffer

open DICE.Definitions


val uds_len : hashable_len


/// The model maintains some abstract local state
///
/// The state is a reference to an erased (ghost) value,
///   and so, we can be sure that it doesn't impact the concrete executions
///
/// This type can be left out of the native C implementation of this interface


noextract
val local_state : (a:Type0 & pre:P.preorder (G.erased a) & HST.mref (G.erased a) pre)


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
: (b:B.buffer uint8{B.length b == v uds_len /\ B.freeable b})

val get_cdi (st:state)
: (b:B.buffer uint8{B.length b == v cdi_len /\ B.freeable b})

val get_uds_value (st:state)
: GTot (s:Seq.seq uint8{Seq.length s == v uds_len})

val get_riot_header (st:state)
: riot_header_t


/// Helper

unfold
let contains (h:HS.mem) (st:state) =
  B.live h (get_uds st) /\
  B.live h (get_cdi st) /\
  h `contains_riot_header` (get_riot_header st)

unfold
let disjointness (st:state) =
  let (| _, _, local_st |) = local_state in
  let rh = get_riot_header st in
  B.all_disjoint ([
    B.loc_buffer (get_uds st);
    B.loc_buffer (get_cdi st);
    B.loc_mreference local_st;
    B.loc_buffer rh.binary_hash;
    B.loc_buffer rh.header_sig;
    B.loc_buffer rh.binary;
    B.loc_buffer rh.pubkey])


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
: HST.ST state
  (requires fun h ->
    uds_is_uninitialized h)
  (ensures fun h0 st h1 ->
    uds_is_initialized /\  //uds has been initialized
    (let (| _, _, local_st |) = local_state in
     let uds  = get_uds st in
     h1 `HS.contains` local_st /\
     h1 `contains` st /\
     B.(modifies (loc_mreference local_st) h0 h1) /\
     disjointness st /\
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
