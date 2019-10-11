module Test1

open FStar.Integers
open FStar.HyperStack.ST

module S   = FStar.Seq
module IB  = LowStar.ImmutableBuffer
module B   = LowStar.Buffer
module M   = LowStar.Modifies
module HS  = FStar.HyperStack
module HST = FStar.HyperStack.ST

let BYTE = uint_8

let _DICE_DIGEST_LENGTH = 0x20ul
let _DICE_UDS_LENGTH    = 0x20ul

/// 1. IB? 2. UDS length?
let _UDS //: IB.libuffer uint_8 (v _DICE_UDS_LENGTH)
          = IB.igcmalloc_of_list HS.root [
    0xb5uy; 0x85uy; 0x94uy; 0x93uy; 0x66uy; 0x1euy; 0x2euy; 0xaeuy;
    0x96uy; 0x77uy; 0xc5uy; 0x5duy; 0x59uy; 0x0buy; 0x92uy; 0x94uy;
    0xe0uy; 0x94uy; 0xabuy; 0xafuy; 0xd7uy; 0x40uy; 0x78uy; 0x7euy;
    0x05uy; 0x0duy; 0xfeuy; 0x6duy; 0x85uy; 0x90uy; 0x53uy; 0xa0uy]

(*)
let main (): ST unit
  (requires fun _ -> True)
  (ensures  fun h _ h' -> True)
=
  push_frame ();
  let _UDS : B.lbuffer uint_8 (v _DICE_UDS_LENGTH)
          = B.alloca_of_list [
    0xb5uy; 0x85uy; 0x94uy; 0x93uy; 0x66uy; 0x1euy; 0x2euy; 0xaeuy;
    0x96uy; 0x77uy; 0xc5uy; 0x5duy; 0x59uy; 0x0buy; 0x92uy; 0x94uy;
    0xe0uy; 0x94uy; 0xabuy; 0xafuy; 0xd7uy; 0x40uy; 0x78uy; 0x7euy;
    0x05uy; 0x0duy; 0xfeuy; 0x6duy; 0x85uy; 0x90uy; 0x53uy; 0xa0uy
    ] in
  let _CDI : B.lbuffer uint_8 (v _DICE_DIGEST_LENGTH)
          = B.alloca 0x00uy _DICE_DIGEST_LENGTH in

  // uint8_t     uDigest[DICE_DIGEST_LENGTH] = { 0 };
  let uDigest : B.lbuffer uint_8 (v _DICE_DIGEST_LENGTH)
              = B.alloca 0x00uy _DICE_DIGEST_LENGTH in

  // uint8_t     rDigest[DICE_DIGEST_LENGTH] = { 0 };
  let rDigest : B.lbuffer uint_8 (v _DICE_DIGEST_LENGTH)
              = B.alloca 0x00uy _DICE_DIGEST_LENGTH in
  pop_frame ()
*)

let main (): Stack C.exit_code
  (requires fun _ -> True)
  (ensures  fun h _ h' -> True)
=
  push_frame ();

  (*
  let uds : B.lbuffer uint_8 (v _DICE_UDS_LENGTH) = B.alloca_of_list [
    0xb5; 0x85; 0x94; 0x93; 0x66; 0x1e; 0x2e; 0xae;
    0x96; 0x77; 0xc5; 0x5d; 0x59; 0x0b; 0x92; 0x94;
    0xe0; 0x94; 0xab; 0xaf; 0xd7; 0x40; 0x78; 0x7e;
    0x05; 0x0d; 0xfe; 0x6d; 0x85; 0x90; 0x53; 0xa0
    ] in
  *)

  let cdi = B.alloca_of_list [0x00] in

  // uint8_t     uDigest[DICE_DIGEST_LENGTH] = { 0 };
  let uDigest : B.lbuffer uint_8 (v _DICE_DIGEST_LENGTH)
              = B.alloca 0x00 _DICE_DIGEST_LENGTH in

  // uint8_t     rDigest[DICE_DIGEST_LENGTH] = { 0 };
  let rDigest : B.lbuffer uint_8 (v _DICE_DIGEST_LENGTH)
              = B.alloca 0x00uy _DICE_DIGEST_LENGTH in

/// Boot:

/// DiceInit:

/// DiceCore:

/// Error:
  pop_frame ();
  C.EXIT_SUCCESS
