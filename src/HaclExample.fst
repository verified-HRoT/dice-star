module HaclExample

open Hacl.Hash.Definitions
open Spec.Hash.Definitions

open Lib.IntTypes

open FStar.HyperStack
open FStar.HyperStack.ST

module HI = Lib.IntTypes
module B = LowStar.Buffer
module SHD = Spec.Hash.Definitions

let hash_example
  (input:B.buffer HI.uint8)
  (len  :FStar.UInt32.t{FStar.UInt32.v len = LowStar.Buffer.length input})
  (hash: Hacl.Hash.Definitions.hash_t Spec.Hash.Definitions.SHA2_512)
: Stack unit
  (requires (fun h ->
      B.live h input /\
      B.live h hash /\
      B.disjoint input hash /\
      B.length input <= SHD.max_input_length SHD.SHA2_512))
  (ensures fun _ _ _ -> True)
=
  push_frame ();

  let h
    : hash_t SHD.SHA2_512
  =
    B.alloca (u8 0x00) (hash_len SHD.SHA2_512)
  in

  Hacl.Hash.SHA2.hash_512
    input
    len
    hash;
  pop_frame ();
  ()
