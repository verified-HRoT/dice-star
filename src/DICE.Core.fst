module DICE.Core

open Common
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

let rec memcpy
  (#a)
  (dst: B.buffer a)
  (src: B.buffer a)
  (len: I.uint_32)
: HST.Stack unit
  (requires fun h ->
      B.live h dst
    /\ B.live h src
    /\ B.disjoint dst src
    /\ len > 0ul
    /\ len <= B.len src
    /\ B.len src <= B.len dst)
  (ensures  fun h0 _ h1 ->
      M.modifies (M.loc_buffer dst) h0 h1
/// TODO: /\ (S.slice (B.as_seq h1 dst) 0 (v len - 1)) `S.equal` (S.slice (B.as_seq h1 src) 0 (v len - 1))
    )
=
  let cur = len - 1ul in
  dst.(cur) <- src.(cur);
  match cur with
  | 0ul -> ()
  | _   -> memcpy dst src cur

let rec memset
  (#a)
  (dst: B.buffer a)
  (v: a)
  (len: I.uint_32)
: HST.Stack unit
  (requires fun h ->
      B.live h dst
    /\ len > 0ul
    /\ len <= B.len dst)
  (ensures  fun h0 _ h1 ->
      M.modifies (M.loc_buffer dst) h0 h1
/// TODO: /\ (S.slice (B.as_seq h1 dst) 0 (v len - 1)) `S.equal` (S.slice (B.as_seq h1 src) 0 (v len - 1))
    )
=
  let cur = len - 1ul in
  dst.(cur) <- v;
  match cur with
  | 0ul -> ()
  | _   -> memset dst v cur

#reset-options "--z3rlimit 50"
#push-options "--query_stats"
let _tmain
  (ret: B.pointer HI.int32)
: HST.Stack unit
  (requires fun h ->
      B.live h ret
    /\ B.live h uds
    /\ B.live h _DEFAULT_LOADER_PATH
    /\ B.live h _DEFAULT_RIOT_PATH)
  (ensures  fun _ _ _ -> True)
=
  HST.push_frame();

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
  let riotImagePath :B.buffer imagePath =
    _DEFAULT_RIOT_PATH in
  let loaderImagePath :B.buffer imagePath =
    _DEFAULT_LOADER_PATH in

/// REF: uint8_t     *riotCore;
/// REF: DWORD       riotSize, offset;
  let riotSize: B.pointer nat
    = B.alloca 0x00 1ul in
  let offset: B.pointer I.uint_32
    = B.alloca 0x00ul 1ul in

///
/// Boot:
///

/// DONE: Load DLL containing RIoT Core
/// TODO: Check return value
/// REF: HINSTANCE   hRiotDLL;
///      hRiotDLL = LoadLibrary(riotImagePath);
  let hRiotDLL: hinstance
    = {addr = B.alloca (HI.u32 0x00) 1ul} in
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
    _DICE_UDS_LENGTH
    uds
    uDigest;

/// DONE: Derive CDI value
/// REF: DiceSHA256_2(uDigest, DICE_DIGEST_LENGTH, rDigest, DICE_DIGEST_LENGTH, CDI);
    let cdi: hash_t SHA2_256
      = B.alloca (HI.u8 0x00) (hash_len SHA2_256) in
    diceSHA256_2
      (hash_length SHA2_256) uDigest
      (hash_length SHA2_256) rDigest
      cdi;

/// TODO: Clean up potentially sensative data
/// REF: memset(uDigest, 0x00, DICE_DIGEST_LENGTH);
///      memset(rDigest, 0x00, DICE_DIGEST_LENGTH);

    memset uDigest (HI.u8 0x00) (hash_len SHA2_256);
    memset rDigest (HI.u8 0x00) (hash_len SHA2_256);

///
/// Start RIoT:
///
    riotStart ({alg=SHA2_256;cdi=cdi});

  ret *= ret_SUCCESS;
  HST.pop_frame()
