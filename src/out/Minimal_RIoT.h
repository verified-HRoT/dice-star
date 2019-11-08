/* 
  This file was generated by KreMLin <https://github.com/FStarLang/kremlin>
  KreMLin invocation: krml -no-prefix Minimal.Main Minimal.Main.fst -skip-compilation -tmpdir out -I /home/zhetao/Sources/hacl-star/specs -I /home/zhetao/Sources/hacl-star/specs/lemmas -I /home/zhetao/Sources/hacl-star/code/hash -I /home/zhetao/Sources/hacl-star/code/hkdf -I /home/zhetao/Sources/hacl-star/code/hmac -I /home/zhetao/Sources/hacl-star/code/curve25519 -I /home/zhetao/Sources/hacl-star/code/ed25519 -I /home/zhetao/Sources/hacl-star/lib -I /home/zhetao/Sources/hacl-star/providers/evercrypt -warn-error +11
  F* version: 953b2211
  KreMLin version: e324b7e6
 */

#include "kremlib.h"
#ifndef __Minimal_RIoT_H
#define __Minimal_RIoT_H

#include "Lib_IntTypes.h"
#include "Spec_Hash_Definitions.h"


extern Spec_Hash_Definitions_hash_alg Minimal_RIoT__RIOT_ALG;

extern uint32_t Minimal_RIoT__RIOT_DIGEST_LENGTH;

extern uint32_t Minimal_RIoT__BIGLEN;

typedef Lib_IntTypes_sec_int_t____ *Minimal_RIoT_bigval_t;

Lib_IntTypes_sec_int_t____
*Minimal_RIoT___proj__Mkbigval_t__item__bigval(Lib_IntTypes_sec_int_t____ *projectee);

typedef struct Minimal_RIoT_affine_point_t_s
{
  Lib_IntTypes_sec_int_t____ *x;
  Lib_IntTypes_sec_int_t____ *y;
  Lib_IntTypes_sec_int_t____ *infinity;
}
Minimal_RIoT_affine_point_t;

Lib_IntTypes_sec_int_t____
*Minimal_RIoT___proj__Mkaffine_point_t__item__x(Minimal_RIoT_affine_point_t projectee);

Lib_IntTypes_sec_int_t____
*Minimal_RIoT___proj__Mkaffine_point_t__item__y(Minimal_RIoT_affine_point_t projectee);

Lib_IntTypes_sec_int_t____
*Minimal_RIoT___proj__Mkaffine_point_t__item__infinity(Minimal_RIoT_affine_point_t projectee);

typedef struct Minimal_RIoT_ecdsa_sig_t_s
{
  Lib_IntTypes_sec_int_t____ *r;
  Lib_IntTypes_sec_int_t____ *s;
}
Minimal_RIoT_ecdsa_sig_t;

Lib_IntTypes_sec_int_t____
*Minimal_RIoT___proj__Mkecdsa_sig_t__item__r(Minimal_RIoT_ecdsa_sig_t projectee);

Lib_IntTypes_sec_int_t____
*Minimal_RIoT___proj__Mkecdsa_sig_t__item__s(Minimal_RIoT_ecdsa_sig_t projectee);

typedef Minimal_RIoT_ecdsa_sig_t Minimal_RIoT_ecc_signature;

typedef Lib_IntTypes_sec_int_t____ *Minimal_RIoT_ecc_privatekey;

typedef Minimal_RIoT_affine_point_t Minimal_RIoT_ecc_publickey;

typedef Minimal_RIoT_affine_point_t Minimal_RIoT_ecc_secret;

typedef Minimal_RIoT_ecdsa_sig_t Minimal_RIoT_riot_ecc_signature;

typedef Minimal_RIoT_affine_point_t Minimal_RIoT_riot_ecc_publickey;

typedef Lib_IntTypes_sec_int_t____ *Minimal_RIoT_riot_ecc_privatekey;

extern void
Minimal_RIoT_riotCrypt_Hash(
  uint32_t resultSize,
  Lib_IntTypes_sec_int_t____ *result,
  uint32_t dataSize,
  Lib_IntTypes_sec_int_t____ *data
);

extern void
Minimal_RIoT_riotCrypt_Hash2(
  uint32_t resultSize,
  Lib_IntTypes_sec_int_t____ *result,
  uint32_t data1Size,
  Lib_IntTypes_sec_int_t____ *data1,
  uint32_t data2Size,
  Lib_IntTypes_sec_int_t____ *data2
);

extern void
Minimal_RIoT_riotCrypt_DeriveEccKey(
  Minimal_RIoT_affine_point_t public_key,
  Lib_IntTypes_sec_int_t____ *private_key,
  Spec_Hash_Definitions_hash_alg digest_alg,
  Lib_IntTypes_sec_int_t____ *digest,
  uint32_t label_size,
  Lib_IntTypes_sec_int_t____ *label
);

extern Lib_IntTypes_sec_int_t____
*Minimal_RIoT_signAliasCert(
  Minimal_RIoT_affine_point_t aliasKeyPub,
  Minimal_RIoT_affine_point_t deviceIDPub,
  uint32_t fwidLen,
  Lib_IntTypes_sec_int_t____ *fwid,
  Lib_IntTypes_sec_int_t____ *privKey
);

#define FStar_Pervasives_Native_None 0
#define FStar_Pervasives_Native_Some 1

typedef uint8_t FStar_Pervasives_Native_option__Minimal_RIoT_affine_point_t_tags;

typedef struct FStar_Pervasives_Native_option__Minimal_RIoT_affine_point_t_s
{
  FStar_Pervasives_Native_option__Minimal_RIoT_affine_point_t_tags tag;
  Minimal_RIoT_affine_point_t v;
}
FStar_Pervasives_Native_option__Minimal_RIoT_affine_point_t;

extern Lib_IntTypes_sec_int_t____
*Minimal_RIoT_signDeviceCert(
  Minimal_RIoT_affine_point_t deviceIDPub,
  FStar_Pervasives_Native_option__Minimal_RIoT_affine_point_t rootKeyPub,
  Lib_IntTypes_sec_int_t____ *privKey
);

extern Lib_IntTypes_sec_int_t____ *Minimal_RIoT_get_FWID();

void Minimal_RIoT_riotStart(uint32_t cdiLen, Lib_IntTypes_sec_int_t____ *cdi);

#define __Minimal_RIoT_H_DEFINED
#endif
