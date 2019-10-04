module RIoTCore


module HS  = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B   = LowStar.Buffer
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

let _UDS = B.malloca_of_list [0;1]

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
