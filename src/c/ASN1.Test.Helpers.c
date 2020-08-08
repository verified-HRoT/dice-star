#include <string.h>
#include <stdio.h>
#include "mbedtls/asn1.h"
#include "mbedtls/asn1write.h"

_Bool buffer_eq (unsigned char *b1, unsigned char *b2, size_t l)
{
  return memcmp (b1, b2, l) == 0;
}

void mbedtls_parse_INTEGER (uint8_t *buf, size_t len, size_t pos)
{
  uint8_t *c;
  c = buf + pos;
  int32_t val;
  mbedtls_asn1_get_int (&c, buf + len, &val);
  printf ("Parsed  : %d\n", val);
  return;
}

void mbedtls_parse_BOOLEAN (uint8_t *buf, size_t len, size_t pos)
{
  uint8_t *c;
  c = buf + pos;
  int32_t val;
  mbedtls_asn1_get_bool (&c, buf + len, &val);
  printf ("Parsed  : %d\n", val);
  return;
}

void mbedtls_parse_ASN1_NULL (uint8_t *buf, size_t len, size_t pos)
{
  // uint8_t *c;
  // c = buf + pos;
  // int ret = mbedtls_asn1_get_tag (&c, buf + len, 0, MBEDTLS_ASN1_NULL);
  // printf("Parsed len: %d", ret);
  printf("mbedTLS does not have ASN1_NULL parser. \n");
  return;
}

void mbedtls_parse_BIT_STRING (uint8_t *buf, size_t len, size_t pos)
{
  uint8_t *c;
  c = buf + pos;
  mbedtls_asn1_bitstring bs;
  mbedtls_asn1_get_bitstring (&c, buf + len, &bs);

  printf("Parsed  : len: %ld; unused_bits: %d; s: ", bs.len, bs.unused_bits);
  for(int i = 1; i <= bs.len; i++){
    printf("0x%x ", bs.p[i-1]);
  }
  printf("\n");

  return;
}

void mbedtls_parse_OCTET_STRING (uint8_t *buf, size_t len, size_t pos)
{
  printf("mbedTLS does not have compatible OCTET STRING parser. \n");
  return;
}

void mbedtls_parse_OID (uint8_t *buf, size_t len, size_t pos)
{
  printf("mbedTLS does not have compatible OID parser. \n");
  return;
}
