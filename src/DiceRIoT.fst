module Test1

open FStar.Integers
open FStar.HyperStack.ST
//open LowStar.Buffer
open LowStar.BufferOps

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

let _DICE_DIGEST_LENGTH : uint_32 = 0x20ul
let _DICE_UDS_LENGTH    : uint_32 = 0x20ul

inline_for_extraction
let udslist : list uint_8
= [0xb5uy; 0x85uy; 0x94uy; 0x93uy; 0x66uy; 0x1euy; 0x2euy; 0xaeuy;
   0x96uy; 0x77uy; 0xc5uy; 0x5duy; 0x59uy; 0x0buy; 0x92uy; 0x94uy;
   0xe0uy; 0x94uy; 0xabuy; 0xafuy; 0xd7uy; 0x40uy; 0x78uy; 0x7euy;
   0x05uy; 0x0duy; 0xfeuy; 0x6duy; 0x85uy; 0x90uy; 0x53uy; 0xa0uy]

(*)
let ibUDS //: IB.libuffer uint_8 (v _DICE_UDS_LENGTH)
          = IB.igcmalloc_of_list HS.root [
    0xb5uy; 0x85uy; 0x94uy; 0x93uy; 0x66uy; 0x1euy; 0x2euy; 0xaeuy;
    0x96uy; 0x77uy; 0xc5uy; 0x5duy; 0x59uy; 0x0buy; 0x92uy; 0x94uy;
    0xe0uy; 0x94uy; 0xabuy; 0xafuy; 0xd7uy; 0x40uy; 0x78uy; 0x7euy;
    0x05uy; 0x0duy; 0xfeuy; 0x6duy; 0x85uy; 0x90uy; 0x53uy; 0xa0uy]

let ibCDI : LowStar.ImmutableBuffer.libuffer UInt8.t
    (UInt32.v (_DICE_DIGEST_LENGTH))
    (Seq.Base.create (UInt32.v (_DICE_DIGEST_LENGTH)) (0x00uy))
    = IB.igcmalloc HS.root 0x00uy _DICE_DIGEST_LENGTH
*)

noeq
type uds_t (len: uint_32) =
| UDS : (B.lbuffer uint_8 (v len)) -> uds_t len

noeq
type cdi_t (len: uint_32) =
| CDI : (B.lbuffer uint_8 (v len)) -> cdi_t len

let _BIGLEN = 9

/// REF:
/// typedef struct {
///     uint32_t data[BIGLEN];
/// } bigval_t;
noeq
type bigval_t = {
     data : B.lbuffer uint_32 _BIGLEN
  }

/// REF:
/// typedef struct {
///     bigval_t x;
///     bigval_t y;
///     uint32_t infinity;
/// } affine_point_t;
noeq
type affine_point_t = {
     x: bigval_t;
     y: bigval_t;
     infinity: B.pointer uint_32
  }

/// REF:
/// typedef struct {
///     bigval_t r;
///     bigval_t s;
/// } ECDSA_sig_t;
noeq
type ecdsa_sig_t = {
     r: bigval_t;
     s: bigval_t
  }

noeq
type riot_ecc_publickey =
| RIoT_ECC_PublicKey : affine_point_t -> riot_ecc_publickey

noeq
type riot_ecc_privatekey =
| RIoT_ECC_PrivateKey : ecdsa_sig_t -> riot_ecc_privatekey

noeq
type digest_t (len: uint_32) =
| Digest : B.lbuffer uint_8 (v len) -> digest_t len

let riotCrypto_Hash
  (#digestLen: uint_32)
  (cDigest : digest_t digestLen)
  (#cdiLen: uint_32)
  (cdi : cdi_t cdiLen)
: ST unit
  (requires fun _ -> True)
  (ensures  fun _ _ _ -> True)
=
  ()

let riotCrypto_DeriveEccKey
  ()
: ST unit
  (requires fun _ -> True)
  (ensures  fun _ _ _ -> True)
=
  ()

let riotStart
  (#cdiLen: uint_32)
  (cdi: cdi_t cdiLen)
: ST unit
  (requires fun _ -> True)
  (ensures  fun _ _ _ -> True)
=
  push_frame();
  let digest : digest_t _DICE_DIGEST_LENGTH
             = Digest (B.alloca 0x00uy _DICE_DIGEST_LENGTH) in
  riotCrypto_Hash digest cdi;
  pop_frame()

/// NOTE: Dice Start Point
let main (): Stack C.exit_code
  (requires fun _ -> True)
  (ensures  fun h _ h' -> True)
=
  push_frame ();

/// REF: const BYTE UDS[DICE_UDS_LENGTH] = {
///    0xb5, 0x85, 0x94, 0x93, 0x66, 0x1e, 0x2e, 0xae,
///    0x96, 0x77, 0xc5, 0x5d, 0x59, 0x0b, 0x92, 0x94,
///    0xe0, 0x94, 0xab, 0xaf, 0xd7, 0x40, 0x78, 0x7e,
///    0x05, 0x0d, 0xfe, 0x6d, 0x85, 0x90, 0x53, 0xa0 };
  let uds : uds_t _DICE_UDS_LENGTH
          = UDS (B.alloca_of_list udslist) in

/// REF: BYTE CDI[DICE_DIGEST_LENGTH] = { 0x00 };
  let cdi : cdi_t _DICE_DIGEST_LENGTH
          = CDI (B.alloca 0x00uy _DICE_DIGEST_LENGTH) in

/// REF: uint8_t     uDigest[DICE_DIGEST_LENGTH] = { 0 };
  let uDigest : B.lbuffer uint_8 (v _DICE_DIGEST_LENGTH)
              = B.alloca 0x00uy _DICE_DIGEST_LENGTH in

/// REF: uint8_t     rDigest[DICE_DIGEST_LENGTH] = { 0 };
  let rDigest : B.lbuffer uint_8 (v _DICE_DIGEST_LENGTH)
              = B.alloca 0x00uy _DICE_DIGEST_LENGTH in

/// REF: TCHAR       *riotImagePath, *loaderImagePath;
/// REF: uint8_t     *riotCore;
/// REF: DWORD       riotSize, offset;
/// REF: HINSTANCE   hRiotDLL;

/// REF: uint8_t     uDigest[DICE_DIGEST_LENGTH] = { 0 };
  let uDigest : B.lbuffer uint_8 (v _DICE_DIGEST_LENGTH)
              = B.alloca 0x00uy _DICE_DIGEST_LENGTH in

/// REF: uint8_t     rDigest[DICE_DIGEST_LENGTH] = { 0 };
  let rDigest : B.lbuffer uint_8 (v _DICE_DIGEST_LENGTH)
              = B.alloca 0x00uy _DICE_DIGEST_LENGTH in

  //riotStart cdi;

  pop_frame ();
  C.EXIT_SUCCESS
