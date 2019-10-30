module RIoT.Stubs

open Common

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

/// <><><><><><><><<><><><><><><><><><><><><><><><><><><><><><><><>
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
/// TODO: /\ (B.get h1 dst (v len)) == (B.get h1 src (v len))
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

let _BIGLEN : I.uint_32 = 0x09ul


/// Size, in bytes, of a RIoT digest using the chosen hash algorithm.
/// REF: #define RIOT_DIGEST_LENGTH      SHA256_DIGEST_LENGTH
let _RIOT_DIGEST_LENGTH : I.uint_32 = hash_len SHA2_256

/// Size, in bytes, of a RIoT HMAC.
/// REF: #define RIOT_HMAC_LENGTH        RIOT_DIGEST_LENGTH
let _RIOT_HMAC_LENGTH = _RIOT_DIGEST_LENGTH

/// Size, in bytes, of internal keys used by the RIoT framework.
/// NOTE:    This number of bytes is used for key derivation.
/// REF: #define RIOT_KEY_LENGTH         RIOT_DIGEST_LENGTH
let _RIOT_KEY_LENGTH = _RIOT_DIGEST_LENGTH

/// Number of bits in internal symmetric keys used by the RIoT framework.
/// NOTE:    This number of bits is used for key derivation. The symmetric
///          algorithm implemenbted by the RIoT framework may use only a
///          subset of these bytes for encryption.
/// REF: #define RIOT_KEY_BITS           (RIOT_KEY_LENGTH * 8)
let _RIOT_KEY_BITS = _RIOT_KEY_LENGTH

/// Number of bytes in symmetric encryption keys used by the RIoT framework.
/// This number also includes IV/Counter bytes.
/// REF: #define RIOT_SYM_KEY_LENGTH             (16 + 16)
let _RIOT_SYM_KEY_LENGT : I.uint_32 = 16ul + 16ul

/// Size, in bytes, of encoded RIoT Key length
/// REF: #define RIOT_ENCODED_BUFFER_MAX         (0x80)
let _RIOT_ENCODED_BUFFER_MAX : I.uint_32 = 0x80ul

/// Maximal number of bytes in a label/context passed to the RIoT KDF routine.
/// REF: #define RIOT_MAX_KDF_CONTEXT_LENGTH     RIOT_DIGEST_LENGTH
let _RIOT_MAX_KDF_CONTEXT_LENGTH : I.uint_32 = _RIOT_DIGEST_LENGTH

/// Maximal number of bytes in a label/context passed to the RIoT KDF routine.
/// REF: #define RIOT_MAX_KDF_LABEL_LENGTH       RIOT_DIGEST_LENGTH
let _RIOT_MAX_KDF_CONTEXT_LABEL_LENGTH : I.uint_32 = _RIOT_DIGEST_LENGTH

/// Maximal number of bytes in a RIOT_AIK certificate
/// REF: #define RIOT_MAX_CERT_LENGTH        2048
let _RIOT_MAX_CERT_LENGTH : I.uint_32 = 2048ul

noeq
type bigval_t = {
     bigval : B.lbuffer HI.uint32 (v _BIGLEN)
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
     infinity: B.pointer HI.uint32
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

type ecc_signature  = ecdsa_sig_t
type ecc_privatekey = bigval_t
type ecc_publickey  = affine_point_t
type ecc_secret     = affine_point_t

type riot_ecc_signature  = ecc_signature
type riot_ecc_publickey  = ecc_publickey
type riot_ecc_privatekey = ecc_privatekey

/// <><><><><><><><<><><><><><><><><><><><><><><><><><><><><><><><>
assume val riotCrypt_Hash
  (# size: I.uint_32)
  (data: B.lbuffer HI.uint8 (v size))
  (# digest_alg: hash_alg)
  (digest: hash_t digest_alg)
: HST.Stack unit
  (requires fun h ->
      B.live h data
    /\ B.live h digest
    /\ B.disjoint data digest)
  (ensures  fun h0 _ h1 ->
      B.modifies (B.loc_buffer digest) h0 h1)

assume val riotCrypt_DeriveEccKey
  (public_key : riot_ecc_publickey)
  (private_key: riot_ecc_privatekey)
  (#digest_alg: hash_alg)
  (digest: hash_t digest_alg)
  (#label_size: I.uint_32)
  (label: B.lbuffer HI.uint8 (I.v label_size))
: HST.Stack unit
  (requires fun h ->
      B.live h public_key.x.bigval
    /\ B.live h public_key.y.bigval
    /\ B.live h public_key.infinity
    /\ B.live h private_key.bigval
    /\ B.live h digest
    /\ B.live h label)
  (ensures  fun h0 _ h1 -> True)

/// Sets tbsData->SerialNumber to a quasi-random value derived from seedData
/// REF: void RiotSetSerialNumber(RIOT_X509_TBS_DATA* tbsData, const uint8_t* seedData, size_t seedLen);
assume val riotCrypt_SeedDRBG
  //TODO: (tbsData: riot_X509_TBS_DATA)
  (#seedLen: I.uint_32)
  (seedData: B.lbuffer HI.uint8 (I.v seedLen))
: HST.Stack unit
  (requires fun h -> True)
  (ensures  fun h0 _ h1 -> True)

/// TODO: RIOT_STATUS

///
/// REF: RIOT_STATUS
///      RiotCrypt_Sign(
///          RIOT_ECC_SIGNATURE     *sig,        // OUT: Signature of data
///          const void             *data,       // IN:  Data to sign
///          size_t                  dataSize,   // IN:  Data size in bytes
///          const RIOT_ECC_PRIVATE *key         // IN:  Signing key
///      )
assume val riotCrypt_Sign
  (sig: riot_ecc_signature)
  (#dataSize: I.uint_32)
  (data: B.lbuffer HI.uint8 (v dataSize))
  (key: riot_ecc_privatekey)
: HST.Stack unit
  (requires fun h -> True)
  (ensures  fun h0 _ h1 -> True)
///      {
///          uint8_t digest[RIOT_DIGEST_LENGTH];
///
///          RiotCrypt_Hash(digest, sizeof(digest), data, dataSize);
///
///          return RIOT_DSASignDigest(digest, key, sig);
///      }
///

///
/// REF: RIOT_STATUS
///      RiotCrypt_SignDigest(
///          RIOT_ECC_SIGNATURE     *sig,            // OUT: Signature of digest
///          const uint8_t          *digest,         // IN:  Digest to sign
///          size_t                  digestSize,     // IN:  Size of the digest in bytes
///          const RIOT_ECC_PRIVATE *key             // IN:  Signing key
///      )
///      {
///          if (digestSize != RIOT_DIGEST_LENGTH) {
///              return RIOT_INVALID_PARAMETER;
///          }
///
///          return RIOT_DSASignDigest(digest, key, sig);
///      }
assume val riotCrypt_SignDigest
  (sig: riot_ecc_signature)
  (#digest_alg: hash_alg)
  (digest: hash_t digest_alg)
  (key: riot_ecc_publickey)
: HST.Stack unit
  (requires fun h -> True)
  (ensures  fun h0 _ h1 -> True)

/// REF: RIOT_STATUS
///      RiotCrypt_Verify(
///          const void                 *data,       // IN: Data to verify signature of
///          size_t                      dataSize,   // IN: Size of data in bytes
///          const RIOT_ECC_SIGNATURE   *sig,        // IN: Signature to verify
///          const RIOT_ECC_PUBLIC      *key         // IN: ECC public key of signer
///      )
///      {
///          uint8_t digest[RIOT_DIGEST_LENGTH];
///
///          RiotCrypt_Hash(digest, sizeof(digest), data, dataSize);
///
///          return RIOT_DSAVerifyDigest(digest, sig, key);
///      }
assume val riotCrypt_Verify
  (#dataSize: I.uint_32)
  (data: B.lbuffer HI.uint8 (v dataSize))
  (sig: riot_ecc_signature)
  (key: riot_ecc_publickey)
: HST.Stack unit
  (requires fun h -> True)
  (ensures  fun h0 _ h1 -> True)

/// REF: RIOT_STATUS
///      RiotCrypt_VerifyDigest(
///          const uint8_t              *digest,     // IN: Digest to verify signature of
///          size_t                      digestSize, // IN: Size of the digest
///          const RIOT_ECC_SIGNATURE   *sig,        // IN: Signature to verify
///          const RIOT_ECC_PUBLIC      *key         // IN: ECC public key of signer
///      )
///      {
///          if (digestSize != RIOT_DIGEST_LENGTH) {
///              return RIOT_INVALID_PARAMETER;
///          }
///
///          return RIOT_DSAVerifyDigest(digest, sig, key);
///      }
assume val riotCrypt_VerifyDigest
  (#digest_alg: hash_alg)
  (digest: hash_t digest_alg)
  (sig: riot_ecc_signature)
  (key: riot_ecc_publickey)
: HST.Stack unit
  (requires fun h -> True)
  (ensures  fun h0 _ h1 -> True)

///
/// REF: RIOT_STATUS
///      RiotCrypt_EccEncrypt(
///          uint8_t                *result,         // OUT: Buffer to receive encrypted data
///          size_t                  resultCapacity, // IN:  Capacity of the result buffer
///          RIOT_ECC_PUBLIC        *ephKey,         // OUT: Ephemeral key to produce
///          const void             *data,           // IN:  Data to encrypt
///          size_t                  dataSize,       // IN:  Data size in bytes
///          const RIOT_ECC_PUBLIC  *key             // IN:  Encryption key
///      )
assume val riotCrypt_EccEncrypt
  (#resultCapacity: I.uint_32)
  (result: B.lbuffer HI.uint8 (v resultCapacity))
  (ephKey: riot_ecc_publickey)
  (#dataSize: I.uint_32)
  (data: B.lbuffer HI.uint8 (v dataSize))
  (key: riot_ecc_publickey)
: HST.Stack unit
  (requires fun h -> True)
  (ensures  fun h0 _ h1 -> True)
///      {
///          ecc_privatekey  ephPriv;
///          ecc_secret      secret;
///          uint8_t         exchKey[RIOT_KEY_LENGTH];
///          RIOT_STATUS     status;
///
///          status = RIOT_GenerateDHKeyPair(ephKey, &ephPriv);
///
///          if (status != RIOT_SUCCESS) {
///              return status;
///          }
///
///          status = RIOT_GenerateShareSecret((RIOT_ECC_PUBLIC *)key, &ephPriv, &secret);
///
///          if (status != RIOT_SUCCESS) {
///              return status;
///          }
///
///          status = RiotCrypt_Kdf(exchKey, sizeof(exchKey),
///                                 (uint8_t *)&secret, sizeof(secret),
///                                 NULL, 0, (const uint8_t*)RIOT_LABEL_EXCHANGE,
///                                 (sizeof(RIOT_LABEL_EXCHANGE) - 1),
///                                 sizeof(exchKey));
///
///          if (status != RIOT_SUCCESS) {
///              return status;
///          }
///
///          status = RiotCrypt_SymEncryptDecrypt(result, resultCapacity,
///                                               data, dataSize, exchKey);
///          return status;
///      }
///


///
/// REF: RIOT_STATUS
///      RiotCrypt_EccDecrypt(
///          uint8_t                *result,         // OUT: Buffer to receive decrypted data
///          size_t                  resultCapacity, // IN:  Capacity of the result buffer
///          const void             *data,           // IN:  Data to decrypt
///          size_t                  dataSize,       // IN:  Data size in bytes
///          RIOT_ECC_PUBLIC        *ephKey,         // IN:  Ephemeral key to produce
///          const RIOT_ECC_PRIVATE *key             // IN:  Decryption key
///      )
assume val riotCrypt_EccDecrypt
  (#resultCapacity: I.uint_32)
  (result: B.lbuffer HI.uint8 (v resultCapacity))
  (ephKey: riot_ecc_publickey)
  (#dataSize: I.uint_32)
  (data: B.lbuffer HI.uint8 (v dataSize))
  (key: riot_ecc_privatekey)
: HST.Stack unit
  (requires fun h -> True)
  (ensures  fun h0 _ h1 -> True)
///      {
///          ecc_secret      secret;
///          uint8_t         exchKey[RIOT_KEY_LENGTH];
///          RIOT_STATUS     status;
///
///          status = RIOT_GenerateShareSecret(ephKey, (RIOT_ECC_PRIVATE *)key, &secret);
///
///          if (status != RIOT_SUCCESS) {
///              return status;
///          }
///
///          status = RiotCrypt_Kdf(exchKey, sizeof(exchKey),
///                                 (uint8_t *)&secret, sizeof(secret),
///                                 NULL, 0, (const uint8_t*)RIOT_LABEL_EXCHANGE,
///                                 (sizeof(RIOT_LABEL_EXCHANGE) - 1),
///                                 sizeof(exchKey));
///
///          if (status != RIOT_SUCCESS) {
///              return status;
///          }
///
///          status = RiotCrypt_SymEncryptDecrypt(result, resultCapacity,
///                                               data, dataSize, exchKey);
///          return status;
///      }
///      #endif
///


///
/// REF: RIOT_STATUS
///      RiotCrypt_SymEncryptDecrypt(
///          void       *outData,                  // OUT: Output data
///          size_t      outSize,                  // IN:  Size of output data
///          const void *inData,                   // IN:  Input data
///          size_t      inSize,                   // IN:  Size of input data
///          uint8_t     key[RIOT_SYM_KEY_LENGTH]  // IN/OUT: Symmetric key & IV
///      )
assume val riotCrypt_SymEncryptDecrypt
  (#outSize: I.uint_32)
  (outData: B.lbuffer HI.uint32 (I.v outSize))
  (#inSize: I.uint_32)
  (inData: B.lbuffer HI.uint32 (I.v inSize))
  (key: B.lbuffer HI.uint8 _RIOT_SYM_KEY_LENGT)
: HST.Stack unit
  (requires fun h -> True)
  (ensures  fun h0 _ h1 -> True)
///      {
///          uint8_t             *iv = key + 16;
///          aes128EncryptKey_t  aesKey;
///
///          if (outSize < inSize) {
///              return RIOT_INVALID_PARAMETER;
///          }
///
///          RIOT_AES128_Enable(key, &aesKey);
///          RIOT_AES_CTR_128((const aes128EncryptKey_t*) &aesKey, inData, outData, (uint32_t)inSize, iv);
///          RIOT_AES128_Disable(&aesKey);
///
///          return RIOT_SUCCESS;
///      }

assume val riotCrypt_Sign
  (u:unit)
: HST.Stack unit
  (requires fun h -> True)
  (ensures  fun h0 _ h1 -> True)

assume val riotCrypt_Verify
  (u:unit)
: HST.Stack unit
  (requires fun h -> True)
  (ensures  fun h0 _ h1 -> True)

assume val riotCrypt_ExportEccPub
  (u:unit)
: HST.Stack unit
  (requires fun h -> True)
  (ensures  fun h0 _ h1 -> True)

assume val riotSetSerialNumber
  (u:unit)
: HST.Stack unit
  (requires fun h -> True)
  (ensures  fun h0 _ h1 -> True)

assume val derInitContext
  (u:unit)
: HST.Stack unit
  (requires fun h -> True)
  (ensures  fun h0 _ h1 -> True)

assume val x509GetAliasCertTBS
  (u:unit)
: HST.Stack unit
  (requires fun h -> True)
  (ensures  fun h0 _ h1 -> True)

assume val x509GetRootCertTBS
  (u:unit)
: HST.Stack unit
  (requires fun h -> True)
  (ensures  fun h0 _ h1 -> True)

assume val x509MakeRootCert
  (u:unit)
: HST.Stack unit
  (requires fun h -> True)
  (ensures  fun h0 _ h1 -> True)

assume val x509MakeDeviceCert
  (u:unit)
: HST.Stack unit
  (requires fun h -> True)
  (ensures  fun h0 _ h1 -> True)

assume val x509GetDERCsrTbs
  (u:unit)
: HST.Stack unit
  (requires fun h -> True)
  (ensures  fun h0 _ h1 -> True)

assume val x509GetDERCsr
  (u:unit)
: HST.Stack unit
  (requires fun h -> True)
  (ensures  fun h0 _ h1 -> True)

assume val x509MakeAliasCert
  (u:unit)
: HST.Stack unit
  (requires fun h -> True)
  (ensures  fun h0 _ h1 -> True)

assume val der_to_pem
  (u:unit)
: HST.Stack unit
  (requires fun h -> True)
  (ensures  fun h0 _ h1 -> True)

assume val firmwareEntry
  (u:unit)
: HST.Stack unit
  (requires fun h -> True)
  (ensures  fun h0 _ h1 -> True)
