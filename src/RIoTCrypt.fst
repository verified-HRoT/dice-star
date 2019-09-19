module RIoTCrypt

open FStar.Integers
open LowStar.BufferOps
open FStar.HyperStack.ST
open LowStar.Modifies
open FStar
open LowStar

assume val _RIOT_DIGEST_LENGTH : uint_64

// DONE
// REF: RIOT_STATUS
//      RiotCrypt_Hash(
//          uint8_t        *result,         // OUT: Buffer to receive the digest
//          size_t          resultSize,     // IN:  Capacity of the result buffer
//          const void     *data,           // IN:  Data to hash
//          size_t          dataSize        // IN:  Data size in bytes
//      )
//      {
//          RIOT_HASH_CONTEXT ctx;
//
//          if (resultSize < RIOT_DIGEST_LENGTH) {
//              return RIOT_INVALID_PARAMETER;
//          }
//
//          RiotCrypt_HashInit(&ctx);
//          RiotCrypt_HashUpdate(&ctx, data, dataSize);
//          RiotCrypt_HashFinal(&ctx, result);
//
//          return RIOT_SUCCESS;
//      }
type size_t = uint_64
assume val _RiotCrypt_Hash
  (resultSize : size_t{result < _RIOT_DIGEST_LENGTH})
  (data : LowStar.Buffer.pointer uint_8) // NOTE: const void* ?
  (dataSize : size_t)
  : (result : LowStar.Buffer.pointer uint_8)

// DONE
// REF: RIOT_STATUS
//      RiotCrypt_Hash2(
//          uint8_t        *result,         // OUT: Buffer to receive the digest
//          size_t          resultSize,     // IN:  Capacity of the result buffer
//          const void     *data1,          // IN:  1st operand to hash
//          size_t          data1Size,      // IN:  1st operand size in bytes
//          const void     *data2,          // IN:  2nd operand to hash
//          size_t          data2Size       // IN:  2nd operand size in bytes
//      )
//      {
//          RIOT_HASH_CONTEXT ctx;
//
//          if (resultSize < RIOT_DIGEST_LENGTH) {
//              return RIOT_INVALID_PARAMETER;
//          }
//
//          RiotCrypt_HashInit(&ctx);
//          RiotCrypt_HashUpdate(&ctx, data1, data1Size);
//          RiotCrypt_HashUpdate(&ctx, data2, data2Size);
//          RiotCrypt_HashFinal(&ctx, result);
//
//          return RIOT_SUCCESS;
//      }
assume val _RiotCrypt_Hash2
  (resultSize : nat)
  (data1 : string)
  (data1Size : nat)
  (data2 : string)
  (data2Size : nat)
  : result : string

// DONE
// REF: RIOT_STATUS
//      RiotCrypt_DeriveEccKey(
//          RIOT_ECC_PUBLIC    *publicPart,     // OUT: Derived public key
//          RIOT_ECC_PRIVATE   *privatePart,    // OUT: Derived private key
//          const void         *srcData,        // IN:  Initial data for derivation
//          size_t              srcDataSize,    // IN:  Size of the source data in bytes
//          const uint8_t      *label,          // IN:  Label for derivation (may be NULL)
//          size_t              Deterministic Random Bit GeneratorlabelSize       // IN:  DeriveEccKeySize of the label in bytes
//      )
//      {
//          bigval_t    srcVal  = { 0 };
//          bigval_t   *pSrcVal = NULL;
//
//          if (srcDataSize > sizeof(bigval_t)) {
//              return RIOT_INVALID_PARAMETER;
//          }
//
//          if (srcDataSize == sizeof(bigval_t)) {
//              pSrcVal = (bigval_t *)srcData;
//          } else {
//              memcpy(&srcVal, srcData, srcDataSize);
//              pSrcVal = &srcVal;
//          }
//
//          return RIOT_DeriveDsaKeyPair(publicPart, privatePart,
//                                       pSrcVal, label, labelSize);
//      }
assume val _RiotCrypt_DeriveEccKey
  (srcData : string)
  (srcDataSize : nat)
  (label : nat)
  (labelSize : nat)
  : (publicKey:string * privateKey:string)

// DONE: Sign TBS region
// REF: RIOT_STATUS
//      RiotCrypt_Sign(
//          RIOT_ECC_SIGNATURE     *sig,        // OUT: Signature of data
//          const void             *data,       // IN:  Data to sign
//          size_t                  dataSize,   // IN:  Data size in bytes
//          const RIOT_ECC_PRIVATE *key         // IN:  Signing key
//      )
//      {
//          uint8_t digest[RIOT_DIGEST_LENGTH];
//
//          RiotCrypt_Hash(digest, sizeof(digest), data, dataSize);
//
//          return RIOT_DSASignDigest(digest, key, sig);
//      }

// TODO: should be uint32_t
// NOTE: Should I implement the RiotEcc file?
type bigval_t =
| Mk_bigval_t: data:string -> bigval_t
type _ECDSA_sig_t = (l:bigval_t * r:bigval_t)
type ecc_signature = _ECDSA_sig_t
type _RIOT_ECC_SIGNATURE = ecc_signature
assume val _RiotCrypt_Sign
  (data : _RIOT_ECC_SIGNATURE)
  (dataSize : nat)
  (key : string)
  : string
