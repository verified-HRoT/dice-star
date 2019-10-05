module DiceCore

open LowStar.BufferOps
open LowStar.Modifies
open FStar.HyperStack.ST
  
module HS  = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B   = FStar.Buffer
module M   = LowStar.Modifies
module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U16 = FStar.UInt16
module U8  = FStar.UInt8
module Bytes = FStar.Bytes

let uint64 = U64.t
let uint32 = U32.t
let uint16 = U16.t
let uint8  = U8.t
let bytes   = Bytes.bytes

let _DICE_UDS_LENGTH    : U32.t = 0x20ul
let _DICE_DIGEST_LENGTH : U32.t = 0x20ul

let f () : St unit =
  let l = LowStar.Buffer.malloc HS.root 0uy 8ul in
  LowStar.Buffer.free l

/// FStar.Buffer or LowStar.Buffer?

let test () : St unit =
  let h = B.create 0 8ul in


  let udslist = [
    0xb5; 0x85; 0x94; 0x93; 0x66; 0x1e; 0x2e; 0xae;
    0x96; 0x77; 0xc5; 0x5d; 0x59; 0x0b; 0x92; 0x94;
    0xe0; 0x94; 0xab; 0xaf; 0xd7; 0x40; 0x78; 0x7e;
    0x05; 0x0d; 0xfe; 0x6d; 0x85; 0x90; 0x53; 0xa0
    ] in
  let _UDS = B.malloc HS.root udslist 1ul in
  let y = B.alloca_of_list udslist in
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
assume val _SHA256_DIGEST_LENGTH : U32.t
assume val _RIOT_DIGEST_LENGTH : uint32

assume val _RIOT_LABEL_IDENTITY : uint32
assume val _RIOT_LABEL_IDENTITY_SIZE : uint32
(*
let on_the_heap ():St UInt64.t =
let b = B.malloc HS.root 0uL 64ul in
  b.(0ul) <- 32uL;
  let r = b.(0ul) in
  B.free b;
  r

assume val _fwImage : uint32
assume val _fwSize : uint32

effect ST
  (a:Type)
  (pre :HS.mem -> Type0)
  (post:HS.mem -> a -> HS.mem -> Type0)
= FStar.HyperStack.ST.ST a pre post

effect St (a:Type) = FStar.HyperStack.ST.St a

val _DICEStart
  (riotImagePath   : string)
  (loaderImagePath : string)
: ST unit
  (requires fun h -> True)
  (ensures  fun h0 _ h1 -> True)
let _DICEStart _ =
  let uDigest = B.malloc HS.root 0ul _DICE_DIGEST_LENGTH in
  let rDigest = B.malloc HS.root 0ul _DICE_DIGEST_LENGTH in
  ()
 
