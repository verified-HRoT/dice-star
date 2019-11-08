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
let _BIGLEN : I.uint_32 = 0x09ul

type _RIOT_STATUS =
| RIOT_SUCCESS
| RIOT_FAILURE
| RIOT_INVALID_PARAMETER
| RIOT_LOAD_MODULE_FAILED
| RIOT_BAD_FORMAT
| RIOT_INVALID_BOOT_MODE
| RIOT_INVALID_STATE
| RIOT_INVALID_METADATA
| RIOT_INVALID_DEVICE_ID
| RIOT_INVALID_MODULE
| RIOT_INVALID_MODULE_DIGEST
| RIOT_MODULE_UPDATE_FAILED
| RIOT_METADATA_WRITE_FAILED
| RIOT_STATE_UPDATE_FAILED
| RIOT_INVALID_VENDOR_SIGNING_KEY
| RIOT_INVALID_VENDOR_SIGNATURE
| RIOT_INVALID_DEVICE_SIGNATURE
| RIOT_INVALID_TICKET_SIGNATURE
| RIOT_MODULE_UPDATE_NOT_APPROVED
| RIOT_FAILED_UPDATE_POLICY

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
assume val riotCrypt_DeriveEccKey
  (public_key : riot_ecc_publickey)
  (private_key: riot_ecc_privatekey)
  (digest_alg: hash_alg)
  (digest: hash_t digest_alg)
  (label_size: I.uint_32)
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

/// TODO: RIOT_STATUS

/// Sets tbsData->SerialNumber to a quasi-random value derived from seedData
/// REF: RIOT_STATUS
///      RiotCrypt_SeedDRBG(
///          uint8_t     *bytes,
///          size_t       size
///      )
///      {
///          set_drbg_seed(bytes, size);
///          return RIOT_SUCCESS;
///      }
assume val riotCrypt_SeedDRBG
  //TODO: (tbsData: riot_X509_TBS_DATA)
  (seedLen: I.uint_32)
  (seedData: B.lbuffer HI.uint8 (I.v seedLen))
: HST.Stack unit
  (requires fun h -> True)
  (ensures  fun h0 _ h1 -> True)

///
/// REF: RIOT_STATUS
///      RiotCrypt_Kdf(
///          uint8_t        *result,         // OUT: Buffer to receive the derived bytes
///          size_t          resultSize,     // IN:  Capacity of the result buffer
///          const uint8_t  *source,         // IN:  Initial data for derivation
///          size_t          sourceSize,     // IN:  Size of the source data in bytes
///          const uint8_t  *context,        // IN:  Derivation context (may be NULL)
///          size_t          contextSize,    // IN:  Size of the context in bytes
///          const uint8_t  *label,          // IN:  Label for derivation (may be NULL)
///          size_t          labelSize,      // IN:  Size of the label in bytes
///          uint32_t        bytesToDerive   // IN:  Number of bytesto be produced
///      )
assume val riotCrypt_Kdf
  (resultSize: I.uint_32)
  (result: B.lbuffer HI.uint8 (I.v resultSize))
  (sourceSize: I.uint_32)
  (source: B.lbuffer HI.uint8 (I.v sourceSize))
  (contextSize: I.uint_32)
  (context: B.lbuffer HI.uint8 (I.v contextSize))
  (labelSize: I.uint_32)
  (label: B.lbuffer HI.uint8 (I.v labelSize))
  (bytesToDerive: I.uint_32)
: HST.Stack unit
  (requires fun h -> True)
  (ensures  fun h0 _ h1 -> True)
///      {
///          uint8_t  fixed[RIOT_MAX_KDF_FIXED_SIZE];
///          size_t   fixedSize = sizeof(fixed);
///          uint32_t counter = 0;
///
///          if (contextSize > RIOT_MAX_KDF_CONTEXT_LENGTH ||
///              labelSize > RIOT_MAX_KDF_LABEL_LENGTH ||
///              bytesToDerive > resultSize ||
///              bytesToDerive % RIOT_KEY_LENGTH != 0) {
///              return RIOT_INVALID_PARAMETER;
///          }
///
///          fixedSize = RIOT_KDF_FIXED(fixed, fixedSize, label, labelSize,
///                                     context, contextSize, bytesToDerive * 8);
///
///          while (counter < (bytesToDerive / (RIOT_KEY_LENGTH))) {
///
///              RIOT_KDF_SHA256(result + (counter * (RIOT_KEY_LENGTH)),
///                              source, sourceSize, &counter,
///                              fixed, fixedSize);
///          }
///
///          return RIOT_SUCCESS;
///      }
///
///      typedef RIOT_SHA256_CONTEXT     RIOT_HASH_CONTEXT;
///
///      #define RiotCrypt_HashInit      RIOT_SHA256_Init
///      #define RiotCrypt_HashUpdate    RIOT_SHA256_Update
///      #define RiotCrypt_HashFinal     RIOT_SHA256_Final
///


///
/// REF: RIOT_STATUS
///      RiotCrypt_Hash(
///          uint8_t        *result,         // OUT: Buffer to receive the digest
///          size_t          resultSize,     // IN:  Capacity of the result buffer
///          const void     *data,           // IN:  Data to hash
///          size_t          dataSize        // IN:  Data size in bytes
///      )
assume val riotCrypt_Hash
  (resultSize: I.uint_32)
  (result: B.lbuffer HI.uint8 (I.v resultSize))
  (dataSize: I.uint_32)
  (data: B.lbuffer HI.uint8 (I.v dataSize))
: HST.Stack unit
  (requires fun h -> True)
  (ensures  fun h0 _ h1 -> True)
///      {
///          RIOT_HASH_CONTEXT ctx;
///
///          if (resultSize < RIOT_DIGEST_LENGTH) {
///              return RIOT_INVALID_PARAMETER;
///          }
///
///          RiotCrypt_HashInit(&ctx);
///          RiotCrypt_HashUpdate(&ctx, data, dataSize);
///          RiotCrypt_HashFinal(&ctx, result);
///
///          return RIOT_SUCCESS;
///      }
///


///
/// REF: RIOT_STATUS
///      RiotCrypt_Hash2(
///          uint8_t        *result,         // OUT: Buffer to receive the digest
///          size_t          resultSize,     // IN:  Capacity of the result buffer
///          const void     *data1,          // IN:  1st operand to hash
///          size_t          data1Size,      // IN:  1st operand size in bytes
///          const void     *data2,          // IN:  2nd operand to hash
///          size_t          data2Size       // IN:  2nd operand size in bytes
///      )
assume val riotCrypt_Hash2
  (resultSize: I.uint_32)
  (result: B.lbuffer HI.uint8 (I.v resultSize))
  (data1Size: I.uint_32)
  (data1: B.lbuffer HI.uint8 (I.v data1Size))
  (data2Size: I.uint_32)
  (data2: B.lbuffer HI.uint8 (I.v data2Size))
: HST.Stack unit
  (requires fun h -> True)
  (ensures  fun h0 _ h1 -> True)
///      {
///          RIOT_HASH_CONTEXT ctx;
///
///          if (resultSize < RIOT_DIGEST_LENGTH) {
///              return RIOT_INVALID_PARAMETER;
///          }
///
///          RiotCrypt_HashInit(&ctx);
///          RiotCrypt_HashUpdate(&ctx, data1, data1Size);
///          RiotCrypt_HashUpdate(&ctx, data2, data2Size);
///          RiotCrypt_HashFinal(&ctx, result);
///
///          return RIOT_SUCCESS;
///      }
///
///      typedef RIOT_HMAC_SHA256_CTX    RIOT_HMAC_CONTEXT;
///
///      #define RiotCrypt_HmacInit      RIOT_HMAC_SHA256_Init
///      #define RiotCrypt_HmacUpdate    RIOT_HMAC_SHA256_Update
///      #define RiotCrypt_HmacFinal     RIOT_HMAC_SHA256_Final
///


///
/// REF: RIOT_STATUS
///      RiotCrypt_Hmac(
///          uint8_t        *result,         // OUT: Buffer to receive the HMAC
///          size_t          resultCapacity, // IN:  Capacity of the result buffer
///          const void     *data,           // IN:  Data to HMAC
///          size_t          dataSize,       // IN:  Data size in bytes
///          const uint8_t  *key,            // IN:  HMAK key
///          size_t          keySize         // IN:  HMAC key size in bytes
///      )
assume val riotCrypt_Hmac
  (resultSize: I.uint_32)
  (result: B.lbuffer HI.uint8 (I.v resultSize))
  (dataSize: I.uint_32)
  (data: B.lbuffer HI.uint8 (I.v dataSize))
  (keySize: I.uint_32)
  (key: B.lbuffer HI.uint8 (I.v keySize))
: HST.Stack unit
  (requires fun h -> True)
  (ensures  fun h0 _ h1 -> True)
///      {
///          RIOT_HMAC_CONTEXT ctx;
///
///          if (resultCapacity < RIOT_HMAC_LENGTH ||
///              keySize != RIOT_HMAC_LENGTH) {
///              return RIOT_INVALID_PARAMETER;
///          }
///
///          RiotCrypt_HmacInit(&ctx, key, keySize);
///          RiotCrypt_HmacUpdate(&ctx, data, dataSize);
///          RiotCrypt_HmacFinal(&ctx, result);
///
///          return RIOT_SUCCESS;
///      }
///

///
/// REF: RIOT_STATUS
///      RiotCrypt_Hmac2(
///          uint8_t        *result,         // OUT: Buffer to receive the HMAK
///          size_t          resultCapacity, // IN:  Capacity of the result buffer
///          const void     *data1,          // IN:  1st operand to HMAC
///          size_t          data1Size,      // IN:  1st operand size in bytes
///          const void     *data2,          // IN:  2nd operand to HMAC
///          size_t          data2Size,      // IN:  2nd operand size in bytes
///          const uint8_t  *key,            // IN:  HMAK key
///          size_t          keySize         // IN:  HMAC key size in bytes
///      )
assume val riotCrypt_Hmac2
  (resultSize: I.uint_32)
  (result: B.lbuffer HI.uint8 (I.v resultSize))
  (data1Size: I.uint_32)
  (data1: B.lbuffer HI.uint8 (I.v data1Size))
  (data2Size: I.uint_32)
  (data2: B.lbuffer HI.uint8 (I.v data2Size))
  (keySize: I.uint_32)
  (key: B.lbuffer HI.uint8 (I.v keySize))
: HST.Stack unit
  (requires fun h -> True)
  (ensures  fun h0 _ h1 -> True)
///      {
///          RIOT_HMAC_CONTEXT ctx;
///
///          if (resultCapacity < RIOT_HMAC_LENGTH ||
///              keySize != RIOT_HMAC_LENGTH) {
///              return RIOT_INVALID_PARAMETER;
///          }
///
///          RiotCrypt_HmacInit(&ctx, key, keySize);
///          RiotCrypt_HmacUpdate(&ctx, data1, data1Size);
///          RiotCrypt_HmacUpdate(&ctx, data2, data2Size);
///          RiotCrypt_HmacFinal(&ctx, result);
///
///          return RIOT_SUCCESS;
///      }
///
/// REF: RIOT_STATUS
///      RiotCrypt_DeriveEccKey(
///          RIOT_ECC_PUBLIC    *publicPart,     // OUT: Derived public key
///          RIOT_ECC_PRIVATE   *privatePart,    // OUT: Derived private key
///          const void         *srcData,        // IN:  Initial data for derivation
///          size_t              srcDataSize,    // IN:  Size of the source data in bytes
///          const uint8_t      *label,          // IN:  Label for derivation (may be NULL)
///          size_t              labelSize       // IN:  Size of the label in bytes
///      )
///      {
///          bigval_t    srcVal  = { 0 };
///          bigval_t   *pSrcVal = NULL;
///
///          if (srcDataSize > sizeof(bigval_t)) {
///              return RIOT_INVALID_PARAMETER;
///          }
///
///          if (srcDataSize == sizeof(bigval_t)) {
///              pSrcVal = (bigval_t *)srcData;
///          } else {
///              memcpy(&srcVal, srcData, srcDataSize);
///              pSrcVal = &srcVal;
///          }
///
///          return RIOT_DeriveDsaKeyPair(publicPart, privatePart,
///                                       pSrcVal, label, labelSize);
///      }
///
///      void
///      RiotCrypt_ExportEccPub(
///          RIOT_ECC_PUBLIC     *a,     // IN:  ECC Public Key to export
///          uint8_t             *b,     // OUT: Buffer to receive the public key
///          uint32_t            *s      // OUT: Pointer to receive the buffer size (may be NULL)
///      )
///      {
///          *b++ = 0x04;
///          BigValToBigInt(b, &a->x);
///          b += RIOT_ECC_COORD_BYTES;
///          BigValToBigInt(b, &a->y);
///          if (s) {
///              *s = 1 + 2 * RIOT_ECC_COORD_BYTES;
///          }
///      }


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
  (dataSize: I.uint_32)
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
  (digest_alg: hash_alg)
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
  (dataSize: I.uint_32)
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
  (digest_alg: hash_alg)
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
  (resultCapacity: I.uint_32)
  (result: B.lbuffer HI.uint8 (v resultCapacity))
  (ephKey: riot_ecc_publickey)
  (dataSize: I.uint_32)
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
  (resultCapacity: I.uint_32)
  (result: B.lbuffer HI.uint8 (v resultCapacity))
  (ephKey: riot_ecc_publickey)
  (dataSize: I.uint_32)
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
  (outSize: I.uint_32)
  (outData: B.lbuffer HI.uint32 (I.v outSize))
  (inSize: I.uint_32)
  (inData: B.lbuffer HI.uint32 (I.v inSize))
  (key: B.lbuffer HI.uint8 (v _RIOT_SYM_KEY_LENGT))
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

/// REF: OIDs.  Note that the encoder expects a -1 sentinel.
///      static int riotOID[] = { 2,23,133,5,4,1,-1 };
///      static int ecdsaWithSHA256OID[] = { 1,2,840,10045,4,3,2,-1 };
///      static int ecPublicKeyOID[] = { 1,2,840,10045, 2,1,-1 };
///      static int prime256v1OID[] = { 1,2,840,10045, 3,1,7,-1 };
///      static int keyUsageOID[] = { 2,5,29,15,-1 };
///      static int extKeyUsageOID[] = { 2,5,29,37,-1 };
///      static int extAuthKeyIdentifierOID[] = { 2,5,29,35,-1 };
///      static int subjectAltNameOID[] = { 2,5,29,17,-1 };
///      static int clientAuthOID[] = { 1,3,6,1,5,5,7,3,2,-1 };
///      static int sha256OID[] = { 2,16,840,1,101,3,4,2,1,-1 };
///      static int commonNameOID[] = { 2,5,4,3,-1 };
///      static int countryNameOID[] = { 2,5,4,6,-1 };
///      static int orgNameOID[] = { 2,5,4,10,-1 };
///      static int basicConstraintsOID[] = { 2,5,29,19,-1 };

let riotOID: list HI.int32 = [HI.i32 2; HI.i32 23; HI.i32 133; HI.i32 5; HI.i32 4; HI.i32 1; HI.i32 (-1)]

(*)
let ecPublicKeyOID:HI.int32 = [HI.i32 1; HI.i32 2; HI.i32 840; HI.i32 10045; HI.i32  2; HI.i32 1; HI.i32 (-1)]
let prime256v1OID:HI.int32 = [HI.i32 1; HI.i32 2; HI.i32 840; HI.i32 10045; HI.i32  3; HI.i32 1; HI.i32 7; HI.i32 (-1)]
let keyUsageOID:HI.int32 = [HI.i32 2; HI.i32 5; HI.i32 29; HI.i32 15; HI.i32 (-1)]
let extKeyUsageOID:HI.int32 = [HI.i32 2; HI.i32 5; HI.i32 29; HI.i32 37; HI.i32 (-1)]
let extAuthKeyIdentifierOID:HI.int32 = [HI.i32 2; HI.i32 5; HI.i32 29; HI.i32 35; HI.i32 (-1)]
let subjectAltNameOID:HI.int32 = [HI.i32 2; HI.i32 5; HI.i32 29; HI.i32 17; HI.i32 (-1)]
let clientAuthOID:HI.int32 = [HI.i32 1; HI.i32 3; HI.i32 6; HI.i32 1; HI.i32 5; HI.i32 5; HI.i32 7; HI.i32 3; HI.i32 2; HI.i32 (-1)]
let sha256OID:HI.int32 = [HI.i32 2; HI.i32 16; HI.i32 840; HI.i32 1; HI.i32 101; HI.i32 3; HI.i32 4; HI.i32 2; HI.i32 1; HI.i32 (-1)]
let commonNameOID:HI.int32 = [HI.i32 2; HI.i32 5; HI.i32 4; HI.i32 3; HI.i32 (-1)]
let countryNameOID:HI.int32 = [HI.i32 2; HI.i32 5; HI.i32 4; HI.i32 6; HI.i32 (-1)]
let orgNameOID:HI.int32 = [HI.i32 2; HI.i32 5; HI.i32 4; HI.i32 10; HI.i32 (-1)]
let basicConstraintsOID:HI.int32 = [HI.i32 2; HI.i32 5; HI.i32 29; HI.i32 19; HI.i32 (-1)]



///
/// REF: int
///      X509GetAliasCertTBS(
///          DERBuilderContext   *Tbs,
///          RIOT_X509_TBS_DATA  *TbsData,
///          RIOT_ECC_PUBLIC     *AliasKeyPub,
///          RIOT_ECC_PUBLIC     *DevIdKeyPub,
///          uint8_t             *Fwid,
///          uint32_t             FwidLen
///      )
// assume val x509GetAliasCertTBS
//   (tbs: derBuilderContext)
//   (tbsData: riot_x509_tbs_data)
// : HST.Stack unit
//   (requires fun h -> True)
//   (ensures  fun h0 _ h1 -> True)
///      {...}
///


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
*)
