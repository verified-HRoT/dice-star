/* Automatically generated by the Kremlin tool */



#ifndef __ASN1_X509_H
#define __ASN1_X509_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include "LowStar_Printf.h"
#include <string.h>


#include "Hacl_Lib.h"

#define PRIMITIVE 0
#define CONSTRUCTED 1

typedef uint8_t asn1_tag_form_t;

#define APPLICATION 0
#define CONTEXT_SPECIFIC 1
#define PRIVATE 2

typedef uint8_t asn1_tag_class_t;

#define BOOLEAN 0
#define INTEGER 1
#define ASN1_NULL 2
#define OCTET_STRING 3
#define PRINTABLE_STRING 4
#define IA5_STRING 5
#define BIT_STRING 6
#define OID 7
#define UTC_TIME 8
#define Generalized_Time 9
#define SEQUENCE 10
#define SET 11
#define CUSTOM_TAG 12

typedef uint8_t asn1_tag_t_tags;

typedef struct asn1_tag_t_s
{
  asn1_tag_t_tags tag;
  asn1_tag_class_t tag_class;
  asn1_tag_form_t tag_form;
  uint8_t tag_value;
}
asn1_tag_t;

#define OID_RIOT 0
#define OID_AT_CN 1
#define OID_AT_COUNTRY 2
#define OID_AT_ORGANIZATION 3
#define OID_CLIENT_AUTH 4
#define OID_AUTHORITY_KEY_IDENTIFIER 5
#define OID_KEY_USAGE 6
#define OID_EXTENDED_KEY_USAGE 7
#define OID_BASIC_CONSTRAINTS 8
#define OID_DIGEST_SHA256 9
#define OID_EC_ALG_UNRESTRICTED 10
#define OID_EC_GRP_SECP256R1 11
#define OID_ED25519 12
#define OID_X25519 13
#define OID_PKCS9_CSR_EXT_REQ 14

typedef uint8_t oid_t;

typedef struct bit_string_t_s
{
  uint32_t bs_len;
  uint32_t bs_unused_bits;
  FStar_Bytes_bytes bs_s;
}
bit_string_t;

typedef struct octet_string_t_s
{
  uint32_t len;
  FStar_Bytes_bytes s;
}
octet_string_t;

uint32_t
serialize32_flbytes32_backwards(uint32_t len, FStar_Bytes_bytes x, uint8_t *b, uint32_t pos);

uint32_t len_of_asn1_length(uint32_t len);

uint32_t
serialize32_asn1_length_of_type_backwards(
  asn1_tag_t _a,
  uint32_t len,
  uint8_t *b,
  uint32_t pos
);

uint8_t encode_asn1_tag(asn1_tag_t a);

uint32_t len_of_oid(oid_t oid);

uint32_t serialize32_asn1_oid_TLV_backwards(oid_t x, uint8_t *b, uint32_t pos);

uint32_t serialize32_asn1_bit_string_TLV_backwards(bit_string_t x, uint8_t *b, uint32_t pos);

typedef struct character_string_t_s
{
  uint32_t fst;
  FStar_Bytes_bytes snd;
}
character_string_t;

uint32_t FStar_Pervasives_dfst__uint32_t_FStar_Bytes_bytes(character_string_t t);

FStar_Bytes_bytes FStar_Pervasives_dsnd__uint32_t_FStar_Bytes_bytes(character_string_t t);

uint32_t
serialize32_asn1_octet_string_TLV_with_tag_backwards(
  asn1_tag_t a,
  octet_string_t x,
  uint8_t *b,
  uint32_t pos
);

uint32_t len_of_asn1_integer(int32_t value);

uint32_t serialize32_asn1_integer_TLV_backwards(int32_t x, uint8_t *b, uint32_t pos);

uint32_t serialize32_asn1_boolean_TLV_backwards(bool x, uint8_t *input, uint32_t pos);

uint32_t serialize32_asn1_boolean_TLV_false_backwards(bool x, uint8_t *input, uint32_t pos);

extern asn1_tag_t x509_authKeyID_keyIdentifier_tag;

typedef struct key_usage_t_s
{
  oid_t fst;
  int32_t snd;
}
key_usage_t;

uint32_t serialize32_x509_key_usage_backwards(key_usage_t x, uint8_t *b, uint32_t pos);

typedef struct K___ASN1_Base_oid_t_ASN1_Base_character_string_t_s
{
  oid_t fst;
  character_string_t snd;
}
K___ASN1_Base_oid_t_ASN1_Base_character_string_t;

uint32_t
serialize32_RDN_COMMON_NAME(
  K___ASN1_Base_oid_t_ASN1_Base_character_string_t x,
  uint8_t *b,
  uint32_t pos
);

uint32_t
serialize32_RDN_ORGANIZATION(
  K___ASN1_Base_oid_t_ASN1_Base_character_string_t x,
  uint8_t *b,
  uint32_t pos
);

uint32_t
serialize32_RDN_COUNTRY(
  K___ASN1_Base_oid_t_ASN1_Base_character_string_t x,
  uint8_t *b,
  uint32_t pos
);

extern asn1_tag_t x509_extensions_outmost_explicit_tag;

uint32_t len_of_x509_extensions(uint32_t len_payload);

extern uint8_t x509_validity_notBefore_default_buffer[13U];

extern uint8_t x509_validity_notAfter_default_buffer[15U];

typedef struct x509_validity_payload_t_s
{
  FStar_Bytes_bytes notBefore;
  FStar_Bytes_bytes notAfter;
}
x509_validity_payload_t;

uint32_t
serialize32_x509_validity_backwards(x509_validity_payload_t x, uint8_t *b, uint32_t pos);

uint32_t serialize32_algorithmIdentifier_backwards(oid_t x, uint8_t *b, uint32_t pos);

typedef struct subjectPublicKeyInfo_payload_t_s
{
  oid_t subjectPubKey_alg;
  bit_string_t subjectPubKey;
}
subjectPublicKeyInfo_payload_t;

uint32_t
serialize32_subjectPublicKeyInfo_backwards(
  subjectPublicKeyInfo_payload_t x,
  uint8_t *b,
  uint32_t pos
);

subjectPublicKeyInfo_payload_t x509_get_subjectPublicKeyInfo(FStar_Bytes_bytes pubkey);

uint32_t len_of_x509_serialNumber(octet_string_t x);

uint32_t
serialize32_x509_serialNumber_backwards(octet_string_t x, uint8_t *input, uint32_t pos);

uint32_t serialize32_x509_version_backwards(int32_t x, uint8_t *b, uint32_t pos);

#if defined(__cplusplus)
}
#endif

#define __ASN1_X509_H_DEFINED
#endif
