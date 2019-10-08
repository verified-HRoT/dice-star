module DiceCore

open LowStar.BufferOps
open LowStar.Modifies
open LowStar.Buffer
open FStar.Integers

module HS  = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B   = LowStar.Buffer
module IB  = LowStar.ImmutableBuffer
module M   = LowStar.Modifies

let _DICE_UDS_LENGTH    : uint_32 = 0x20ul
let _DICE_DIGEST_LENGTH : uint_32 = 0x20ul

let f () : HST.St unit =
  let l = LowStar.Buffer.malloc HS.root 0uy 8ul in
  LowStar.Buffer.free l

let x = LowStar.Buffer.malloc HS.root 0uy 8ul

inline_for_extraction let udsContent = [
    0xb5; 0x85; 0x94; 0x93; 0x66; 0x1e; 0x2e; 0xae;
    0x96; 0x77; 0xc5; 0x5d; 0x59; 0x0b; 0x92; 0x94;
    0xe0; 0x94; 0xab; 0xaf; 0xd7; 0x40; 0x78; 0x7e;
    0x05; 0x0d; 0xfe; 0x6d; 0x85; 0x90; 0x53; 0xa0
    ]

let test () : HST.St unit =
  let _UDS = IB.igcmalloc_of_list HS.root udsContent in
  ()

let _CDI = B.malloc HS.root [0x00] _DICE_DIGEST_LENGTH

//let x = B.as_seq HS.root (_CDI)

//let f () : St unit =
//  let b = B.malloc h


let _DEFAULT_RIOT_PATH : string = "riot.dll"
let _DEFAULT_LOADER_PATH : string = "FW.dll"
let _RIOT_ENTRY : string = "RiotStart"

// TODO: Date Types
// TODO: Modules

// NOTE: Getting familiar with F* and DICE/RIoT by simply re-implement reference code (https://github.com/microsoft/RIoT/blob/master/Reference/RIoT/Core/RIoT.cpp) in F*.

(*digest lengths*)
assume val _SHA256_DIGEST_LENGTH : uint_32
assume val _RIOT_DIGEST_LENGTH : uint_32

assume val _RIOT_LABEL_IDENTITY : uint_32
assume val _RIOT_LABEL_IDENTITY_SIZE : uint_32

let on_the_heap () : HST.St UInt64.t =
let b = B.malloc HS.root 0uL 64ul in
  b.(0ul) <- 32uL;
  let r = b.(0ul) in
  B.free b;
  r

assume val _fwImage : uint_32
assume val _fwSize : uint_32

val _DICEStart
  (riotImagePath   : string)
  (loaderImagePath : string)
: HST.ST unit
  (requires fun h -> True)
  (ensures  fun h0 _ h1 -> True)
let _DICEStart _ _ =
  let uDigest = B.malloc HS.root 0ul _DICE_DIGEST_LENGTH in
  let rDigest = B.malloc HS.root 0ul _DICE_DIGEST_LENGTH in
  let _UDS = IB.igcmalloc_of_list HS.root udsContent in
  ()

