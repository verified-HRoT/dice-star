module DICE

open Common

open LowStar.BufferOps
open Lib.IntTypes

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

let _DICE_UDS_LENGTH = 0x20

assume val uds : B.lbuffer uint8 _DICE_UDS_LENGTH

type imagePath =

noeq
type hinstance = {
     addr: B.pointer uint32
  }

assume val loadLibrary
  (path: B.buffer imagePath)
  (hDLL: hinstance)
: HST.Stack unit
  (requires fun h ->
      B.live h path
    /\ B.live h hDLL.addr
    /\ B.disjoint path hDLL.addr)
  (ensures fun h0 r h1 ->
      B.modifies (B.loc_buffer hDLL.addr) h0 h1)

assume val _DEFAULT_RIOT_PATH: B.buffer imagePath
assume val _DEFAULT_LOADER_PATH: B.buffer imagePath

noeq
type cdi_t = {
     alg: hash_alg;
     cdi: hash_t alg;
  }

let fpRiotStart =
  (cdi: cdi_t)
-> HST.Stack unit
  (requires fun _ -> True)
  (ensures  fun _ _ _ -> True)

type entryPoint =
assume val _RIOT_ENTRY: entryPoint
assume val getProcAddress
  (hDLL: hinstance)
  (entry: entryPoint)
: fpRiotStart

assume val diceGetRiotInfo
  (hDLL: hinstance)
  (offset: B.pointer I.uint_32)
  (riotSize: B.pointer nat)
: HST.Stack unit
  (requires fun h ->
      h `B.live` hDLL.addr
    /\ h `B.live` offset
    /\ h `B.live` riotSize
    /\ hDLL.addr `B.disjoint` offset
    /\ hDLL.addr `B.disjoint` riotSize
    /\ riotSize  `B.disjoint` offset)
  (ensures  fun h0 _ h1 ->
      B.modifies (B.loc_buffer offset) h0 h1
    /\ B.modifies (B.loc_buffer riotSize) h0 h1)

assume val diceSHA256
  (size : nat)
  (data: B.lbuffer uint8 size)
  (digest: hash_t SHA2_256)
: HST.Stack unit
  (requires fun h ->
      B.live h data
    /\ B.live h digest
    /\ B.disjoint data digest)
  (ensures  fun h0 _ h1 ->
      B.modifies (B.loc_buffer digest) h0 h1)

assume val diceSHA256_2
  (size1 : nat)
  (data1: B.lbuffer uint8 size1)
  (size2 : nat)
  (data2 : B.lbuffer uint8 size2)
  (digest: hash_t SHA2_256)
: HST.Stack unit
  (requires fun h ->
      B.live h data1
    /\ B.live h data2
    /\ B.live h digest
    /\ B.disjoint data1 data2
    /\ B.disjoint data1 digest
    /\ B.disjoint data2 digest)
  (ensures  fun h0 _ h1 ->
      B.modifies (B.loc_buffer digest) h0 h1)

#reset-options "--z3rlimit 50 --max_fuel 50 --max_ifuel 50"
#push-options "--query_stats"
let _tmain
  (ret: B.pointer int32)
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
    B.alloca (u8 0x00) (hash_len SHA2_256) in

/// DONE: Init RIoT Invariant Code Digest
/// REF: uint8_t     rDigest[DICE_DIGEST_LENGTH] = { 0 };
  let rDigest :hash_t SHA2_256 =
    B.alloca (u8 0x00) (hash_len SHA2_256) in

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
    = {addr = B.alloca (u32 0x00) 1ul} in
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
  diceGetRiotInfo hRiotDLL offset riotSize;


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
      = B.alloca (u8 0x00) (hash_len SHA2_256) in
    diceSHA256_2
      (hash_length SHA2_256) uDigest
      (hash_length SHA2_256) rDigest
      cdi;

/// TODO: Clean up potentially sensative data
/// REF: memset(uDigest, 0x00, DICE_DIGEST_LENGTH);
///      memset(rDigest, 0x00, DICE_DIGEST_LENGTH);

///
/// Start RIoT:
///
    riotStart ({alg=SHA2_256;cdi=cdi});

  ret *= ret_TRUE;
  HST.pop_frame()
