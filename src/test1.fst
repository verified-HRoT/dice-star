module Test1

open FStar.HyperStack.ST

module S = FStar.Seq
module B = LowStar.Buffer
module M = LowStar.Modifies
module U32 = FStar.UInt32
module ST = FStar.HyperStack.ST

let _DICE_DIGEST_LENGTH = 0x20ul

let main (): Stack C.exit_code
  (requires fun _ -> True)
  (ensures  fun h _ h' -> True)
=
  push_frame ();
  let uds = B.alloca_of_list [
    0xb5; 0x85; 0x94; 0x93; 0x66; 0x1e; 0x2e; 0xae;
    0x96; 0x77; 0xc5; 0x5d; 0x59; 0x0b; 0x92; 0x94;
    0xe0; 0x94; 0xab; 0xaf; 0xd7; 0x40; 0x78; 0x7e;
    0x05; 0x0d; 0xfe; 0x6d; 0x85; 0x90; 0x53; 0xa0
    ] in
  let cdi = B.alloca_of_list [0x00] in
  let uDigest = B.alloca 0x00uy _DICE_DIGEST_LENGTH in
  let rDigest = B.alloca 0x00uy _DICE_DIGEST_LENGTH in
  pop_frame ();
  C.EXIT_SUCCESS
