module Dice

open FStar.Integers
open FStar.HyperStack.ST

module Seq = FStar.Seq

module HS = FStar.HyperStack
module B  = LowStar.Buffer

type u8 = uint_8

(*** Interface from the crypto library ***)

/// Adding assume val declarations for what we expect from the crypto library
///
/// In actual implementation they will not be assumed, and also the interface will vary from what is sketched below


/// This is a mathematical function that describes what the hash is
///
/// It works over (pure) sequences of bytes

assume val hash (s:Seq.seq u8) : Seq.seq u8


/// The following will be a low-level function, operating on buffers, that computes the hash
///
/// This actual implementation could well differ from how the function is described in the spec hash above
///   For example, the hash could use multiplication whereas the implementation uses repeated additions
///
/// In any case, it provides the postcondition that whatever it computes, no matter how, is functionally same as the hash function
///
/// The functional specification is written in terms of sequence representation of the buffers
///
/// In the actual implementation, there will be more details, like lengths of src and dst may be passed around etc.

assume val hash_impl (src:B.buffer u8) (dst:B.buffer u8)
: ST unit
  (requires fun h -> B.live h src /\ B.live h dst /\ B.disjoint src dst)
  (ensures fun h0 _ h1 ->
    B.modifies (B.loc_buffer dst) h0 h1 /\  //important for framing, so that the callers can derive that buffers that are disjoint from dst did not change
    B.as_seq h1 dst == hash (B.as_seq h0 src))


/// hmac below is similar

assume val hmac (key:Seq.seq u8) (s:Seq.seq u8) : Seq.seq u8

assume val hmac_impl (key:B.buffer u8) (s:B.buffer u8) (dst:B.buffer u8)
: ST unit
  (requires fun h ->
    B.all_live h [B.buf key; B.buf s; B.buf dst] /\
    B.all_disjoint [B.loc_buffer key; B.loc_buffer s; B.loc_buffer dst])
  (ensures fun h0 _ h1 ->
    B.modifies (B.loc_buffer dst) h0 h1 /\
    B.as_seq h1 dst = hmac (B.as_seq h0 key) (B.as_seq h0 s))



(*** Using this interface in the Dice code ***)


/// A sample function that computes CDI using the crypto interface sketched above
///
/// The function computes the measurement of the riot code, and then computes its hmac using uds as the hmac key
///
/// Note that we pass in a temp buffer to store the measurement in
///
/// The final postcondition captures the CDI functionally


let compute_cdi (riot:B.buffer u8) (uds:B.buffer u8) (cdi:B.buffer u8) (temp:B.buffer u8)
: ST unit
  (requires fun h ->
    B.all_live h [B.buf riot; B.buf uds; B.buf cdi; B.buf temp] /\
    B.all_disjoint [B.loc_buffer riot; B.loc_buffer uds; B.loc_buffer cdi; B.loc_buffer temp])
  (ensures fun h0 _ h1 ->
    B.modifies (B.loc_union (B.loc_buffer cdi) (B.loc_buffer temp)) h0 h1 /\
    B.as_seq h1 cdi == hmac (B.as_seq h0 uds) (hash (B.as_seq h0 riot)))
= hash_impl riot temp;
  hmac_impl uds temp cdi
