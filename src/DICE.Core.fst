/// Reference: https://github.com/microsoft/RIoT/blob/master/Reference/DICE/DiceCore.cpp
module DICE.Core

/// Common definitions
open Common
/// DICE stub definitions
open DICE.Stubs

open LowStar.BufferOps
//open Lib.IntTypes
open FStar.Integers

open Spec.Hash.Definitions
open Hacl.Hash.Definitions

module I  = FStar.Integers
module HI  = Lib.IntTypes

module SHA2= Hacl.Hash.SHA2
module HMAC= Hacl.HMAC
module Ed25519 = Hacl.Ed25519

module CL  = C.Loops
module CE  = C.Endianness
module CF  = C.Failure
module C   = C
module CS  = C.String
module S   = FStar.Seq
module IB  = LowStar.ImmutableBuffer
module B   = LowStar.Buffer
module M   = LowStar.Modifies
module HS  = FStar.HyperStack
module HST = FStar.HyperStack.ST


/// DICE definitions
/// REF: #define DICE_UDS_LENGTH         0x20
///      #define DICE_DIGEST_LENGTH      0x20
let _DICE_UDS_LENGTH    = 0x20
let _DICE_DIGEST_LENGTH = hash_len SHA2_256

/// Simulation-only definitions
/// REF: #define DEFAULT_RIOT_PATH       L"riot.dll"     // Contains RIoT Invariant Code
///      #define DEFAULT_LOADER_PATH     L"FW.dll"       // Our simulated Device Firmware
///      #define RIOT_ENTRY              "RiotStart"     // RIoT Core entry point
assume val _DEFAULT_RIOT_PATH   : string
assume val _DEFAULT_LOADER_PATH : string
assume val _RIOT_ENTRY          : string



/// <><><><><><><><><><><><><><><><><> DICE Core main funtion <><><><><><><><><><><><><><><><><><><


#reset-options "--z3rlimit 50"
let _tmain ()
: HST.Stack C.exit_code
  (requires fun h -> True)
  (ensures  fun _ _ _ -> True)
=
  HST.push_frame();

/// DONE: Get UDS using API
/// REF: None
  let uds : uds_t _DICE_UDS_LENGTH
    = get_UDS _DICE_UDS_LENGTH in

/// DONE: Init UDS digest
/// REF: uint8_t     uDigest[DICE_DIGEST_LENGTH] = { 0 };
  let uDigest :hash_t SHA2_256 =
    B.alloca (HI.u8 0x00) (hash_len SHA2_256) in

/// DONE: Init RIoT Invariant Code Digest
/// REF: uint8_t     rDigest[DICE_DIGEST_LENGTH] = { 0 };
  let rDigest :hash_t SHA2_256 =
    B.alloca (HI.u8 0x00) (hash_len SHA2_256) in

/// DONE: Init default paths
/// TODO: Check paths
/// REF: TCHAR       *riotImagePath, *loaderImagePath;
///      riotImagePath = DEFAULT_RIOT_PATH;
///      loaderImagePath = DEFAULT_LOADER_PATH;
  let riotImagePath   : string = _DEFAULT_RIOT_PATH in
  let loaderImagePath : string = _DEFAULT_LOADER_PATH in

/// REF: uint8_t     *riotCore;
/// REF: DWORD       riotSize, offset;
  let riotSize : B.pointer nat = B.alloca 0x00 1ul in
  let offset   : B.pointer nat = B.alloca 0x00 1ul in

///
/// Boot:
///

/// DONE: Load DLL containing RIoT Core
/// TODO: Check return value
/// REF: HINSTANCE   hRiotDLL;
///      hRiotDLL = LoadLibrary(riotImagePath);
  let hRiotDLL: hinstance
    = B.alloca (HI.u32 0x00) 1ul in
  loadLibrary riotImagePath hRiotDLL;

/// DONE: Locate RiotStart
/// REF: fpRiotStart RiotStart = (fpRiotStart)GetProcAddress(hRiotDLL, RIOT_ENTRY);
///      if (!RiotStart) {
///          fprintf(stderr, "ERROR: Failed to locate RiotStart\n");
///          goto Error;
///      }
  let riotStart: fpRiotStart
    = getProcAddress hRiotDLL _RIOT_ENTRY in

/// DONE: Get base offset and size of RIoT Invariant Code
/// REF: if (!DiceGetRiotInfo(hRiotDLL, &offset, &riotSize)) {
///          fprintf(stderr, "ERROR: Failed to locate RIoT Invariant code\n");
///          goto Error;
///      }
  //diceGetRiotInfo hRiotDLL offset riotSize;


/// TODO: Calculate base VA of RIoT Invariant Code
/// TOOD: Cast
/// REF: riotCore = (uint8_t *)((uint64_t)hRiotDLL + offset);
  //let riotCore : I.uint_32 = (UInt32.uint_to_t (!*offset)) in
  //B.alloca (u8 0x00) (UInt32.uint_to_t !*riotSize) in
    //: B.pointer uint8
    //= B.alloca (to_u8 (!*(hRiotDLL.addr) +. !*offset)) 1ul in
    //= B.offset hRiotDLL.addr !*offset in

///
/// DiceCore:
///

/// TODO: Measure RIoT Invariant Code
/// REF: DiceSHA256(riotCore, riotSize, rDigest);
  //diceSHA256 !*riotSize riotCore rDigest;

/// DONE: Don't use UDS directly
/// REF: DiceSHA256(UDS, DICE_UDS_LENGTH, uDigest);
    diceSHA256
      uds
      uDigest;

/// DONE: Derive CDI value
/// REF: DiceSHA256_2(uDigest, DICE_DIGEST_LENGTH, rDigest, DICE_DIGEST_LENGTH, CDI);
    let cdi: cdi_t SHA2_256
      = B.alloca (HI.u8 0x00) (hash_len SHA2_256) in
    //diceSHA256_2
    //  uDigest
    //  rDigest
    //  cdi;

/// TODO: Clean up potentially sensative data
/// REF: memset(uDigest, 0x00, DICE_DIGEST_LENGTH);
///      memset(rDigest, 0x00, DICE_DIGEST_LENGTH);

    B.fill uDigest (HI.u8 0x00) (hash_len SHA2_256);
    B.fill rDigest (HI.u8 0x00) (hash_len SHA2_256);

///
/// Start RIoT:
///
    riotStart (cdi);

  HST.pop_frame();
  C.EXIT_SUCCESS
