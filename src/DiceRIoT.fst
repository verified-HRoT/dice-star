module DiceRIoT

//open FStar.Integers
//open FStar.HyperStack.ST
//open LowStar.Buffer
open LowStar.BufferOps
open Lib.IntTypes

open Spec.Hash.Definitions
open Hacl.Hash.Definitions

module I  = FStar.Integers
module HI  = Lib.IntTypes

module SHA2= Hacl.Hash.SHA2
module HD  = Hacl.Hash.Definitions
module SHD = Spec.Hash.Definitions

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

let _DICE_DIGEST_LENGTH   : I.uint_32 = 0x20ul
let _DICE_UDS_LENGTH      : I.uint_32 = 0x20ul
let _DER_MAX_PEM          : I.uint_32 = 0x400ul
let _SHA256_DIGEST_LENGTH : I.uint_32 = 0x20ul

let f
  (input:B.buffer uint8)
  (len  :I.uint_32{I.v len = B.length input})
  (hash: hash_t SHA2_512)
: HST.Stack unit
  (requires (fun h ->
      B.live h input /\
      B.live h hash /\
      B.disjoint input hash /\
      B.length input <= SHD.max_input_length SHD.SHA2_512))
  (ensures fun _ _ _ -> True)
=
  HST.push_frame ();
  SHA2.hash_512
    input
    len
    hash;
  HST.pop_frame ();
  ()

inline_for_extraction
let udslist : list uint8
= [u8 0xb5; u8 0x85; u8 0x94; u8 0x93; u8 0x66; u8 0x1e; u8 0x2e; u8 0xae;
   u8 0x96; u8 0x77; u8 0xc5; u8 0x5d; u8 0x59; u8 0x0b; u8 0x92; u8 0x94;
   u8 0xe0; u8 0x94; u8 0xab; u8 0xaf; u8 0xd7; u8 0x40; u8 0x78; u8 0x7e;
   u8 0x05; u8 0x0d; u8 0xfe; u8 0x6d; u8 0x85; u8 0x90; u8 0x53; u8 0xa0]

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
type uds_t (len: I.uint_32) =
| UDS : (data: B.lbuffer uint8 (v len)) -> uds_t len

noeq
type cdi_t (len: I.uint_32) =
| CDI : (data: B.lbuffer uint8 (v len)) -> cdi_t len

noeq
type cert_t (len: I.uint_32) =
| CERT : (data: B.lbuffer uint8 (v len)) -> cert_t len

noeq
type hinstance =
| HINSTANCE : (addr: B.buffer uint64) -> hinstance

/// REF:
/// typedef struct {
///     uint32_t data[BIGLEN];
/// } bigval_t;

let _BIGLEN : I.uint_32 = 0x09ul

noeq
type bigval_t = {
     data : B.lbuffer uint32 (v _BIGLEN)
  }
/// NOTE: BUG?

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
     infinity: B.pointer uint32
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
type digest_t (a: hash_alg) =
| Digest : hash_t a -> digest_t a

/// REF: typedef struct
/// {
///    uint8_t SerialNum[RIOT_X509_SNUM_LEN];
///    const char *IssuerCommon;
///    const char *IssuerOrg;
///    const char *IssuerCountry;
///    const char *ValidFrom;
///    const char *ValidTo;
///    const char *SubjectCommon;
///    const char *SubjectOrg;
///    const char *SubjectCountry;
/// } RIOT_X509_TBS_DATA;
noeq
type riot_x509_tbs_data = {
     serialNum      : B.buffer uint8;
     issuerCommon   : B.buffer uint8;
     issuerOrg      : B.buffer uint8;
     issuerCountry  : B.buffer uint8;
     validForm      : B.buffer uint8;
     validTo        : B.buffer uint8;
     subjectCommon  : B.buffer uint8;
     subjectOrg     : B.buffer uint8;
     subjectCountry : B.buffer uint8
  }

/// <><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
(*)
let riotCrypto_Hash
  (#digestLen: uint_32)
  (cDigest   : digest_t digestLen)
  (#cdiLen   : uint_32)
  (cdi       : cdi_t cdiLen)
: ST unit
  (requires fun _ -> True)
  (ensures  fun _ _ _ -> True)
=
  ()

let riotCrypto_Hash2
  (#digestLen1: uint_32)
  (cDigest1   : digest_t digestLen1)
  (#digestLen2: uint_32)
  (cDigest2   : digest_t digestLen2)
  (#cdiLen   : uint_32)
  (cdi       : cdi_t cdiLen)
: ST unit
  (requires fun _ -> True)
  (ensures  fun _ _ _ -> True)
=
  ()

let riotCrypto_DeriveEccKey
  (deviceIDPub : riot_ecc_publickey)
  (deviceIDPriv: riot_ecc_privatekey)
  (#digestLen  : uint_32)
  (cDigest     : digest_t digestLen)
: ST unit
  (requires fun _ -> True)
  (ensures  fun _ _ _ -> True)
=
  ()
*)


/// <><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
let riotStart
  (#cdiLen: I.uint_32)
  (cdi: cdi_t cdiLen)
: HST.Stack unit
  (requires fun _ ->
///
/// REF: Parameter validation
/// if (!(CDI) || (CDILen != SHA256_DIGEST_LENGTH)) {
///     return;
/// }
///
    (B.len (CDI?.data cdi) = _SHA256_DIGEST_LENGTH))
  (ensures  fun _ _ _ -> True)
=
  HST.push_frame();
///
/// NOTE: Should be global variables?
/// REF: RIOT_ECC_PUBLIC     DeviceIDPub;
///
  let deviceIDPub : riot_ecc_publickey =
    RIoT_ECC_PublicKey ({
      x = {data = B.alloca (u32 0) _BIGLEN};
      y = {data = B.alloca (u32 0) _BIGLEN};
      infinity = B.alloca (u32 0) 1ul
  }) in

///
/// REF: RIOT_ECC_PUBLIC     AliasKeyPub;
///
  let aliasKeyPub : riot_ecc_publickey =
    RIoT_ECC_PublicKey ({
      x = {data = B.alloca (u32 0) _BIGLEN};
      y = {data = B.alloca (u32 0) _BIGLEN};
      infinity = B.alloca (u32 0) 1ul
  }) in

/// REF: RIOT_ECC_PRIVATE     AliasKeyPriv;
  let aliasKeyPriv : riot_ecc_privatekey =
    RIoT_ECC_PrivateKey ({
      r = {data = B.alloca (u32 0) _BIGLEN};
      s = {data = B.alloca (u32 0) _BIGLEN}
  }) in

///
/// REF: char                AliasCert[DER_MAX_PEM];
///
  let aliasCert : cert_t _DER_MAX_PEM =
    CERT (
      B.alloca (u8 0x00) _DER_MAX_PEM
  ) in

///
/// REF: char                DeviceCert[DER_MAX_PEM];
///
  let deviceCert : cert_t _DER_MAX_PEM =
    CERT (
      B.alloca (u8 0x00) _DER_MAX_PEM
  ) in

///
/// REF: char                r00tCert[DER_MAX_PEM];
///
  let r00tCert : cert_t _DER_MAX_PEM =
    CERT (
      B.alloca (u8 0x00) _DER_MAX_PEM
  ) in

/// REF: BYTE                derBuffer[DER_MAX_TBS];

///
/// NOTE: init
/// REF: BYTE                cDigest[RIOT_DIGEST_LENGTH];
///
  let cDigest : hash_t SHA2_512 =
    B.alloca (u8 0x00) (hash_len SHA2_512)
  in

/// TODO: REF: BYTE                FWID[RIOT_DIGEST_LENGTH];

///
/// REF: RIOT_ECC_PRIVATE    deviceIDPriv;
///
  let deviceIDPriv : riot_ecc_privatekey =
    RIoT_ECC_PrivateKey ({
      r = {data = B.alloca (u32 0x00) _BIGLEN};
      s = {data = B.alloca (u32 0x00) _BIGLEN}
  }) in


/// TODO: REF: RIOT_ECC_SIGNATURE  tbsSig;
/// TODO: REF: DERBuilderContext   derCtx;
/// TODO: REF: fpFirmwareEntry     FirmwareEntry;
/// TODO: REF: BYTE               *fwImage;
/// TODO: REF: uint32_t            length, PEMtype;
/// TODO: REF: DWORD               fwSize, offset, i;
/// TODO: REF: HINSTANCE           fwDLL;

//    SHA2.hash_512

//  riotCrypto_Hash
//    cDigest cdi;

//  riotCrypto_DeriveEccKey
//    deviceIDPub
//    deviceIDPriv
//    cDigest;

///
/// REF: Derive Alias key pair from CDI and FWID
///    RiotCrypt_DeriveEccKey(&AliasKeyPub,
///                           &AliasKeyPriv,
///                           cDigest, RIOT_DIGEST_LENGTH,
///                           (const uint8_t *)RIOT_LABEL_ALIAS,
///                           lblSize(RIOT_LABEL_ALIAS));
///
//  riotCrypto_DeriveEccKey
//    aliasKeyPub
//    aliasKeyPriv
//    cDigest;

  HST.pop_frame()

/// <><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
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

  riotStart cdi;

  pop_frame ();
  C.EXIT_SUCCESS
