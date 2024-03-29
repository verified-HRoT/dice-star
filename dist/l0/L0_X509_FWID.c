/* Automatically generated by the Kremlin tool */



#include "L0_X509_FWID.h"

#include "internal/ASN1_X509.h"

uint32_t serialize32_fwid_payload_backwards(fwid_payload_t x, uint8_t *input, uint32_t pos)
{
  uint32_t
  offset2 =
    serialize32_asn1_octet_string_TLV_with_tag_backwards(((asn1_tag_t){ .tag = OCTET_STRING }),
      x.fwid_value,
      input,
      pos);
  uint32_t offset1 = serialize32_asn1_oid_TLV_backwards(x.fwid_hashAlg, input, pos - offset2);
  return offset1 + offset2;
}

uint32_t serialize32_fwid_backwards(fwid_payload_t x, uint8_t *b, uint32_t pos)
{
  uint32_t offset_data = serialize32_fwid_payload_backwards(x, b, pos);
  uint32_t
  offset2 =
    serialize32_asn1_length_of_type_backwards(((asn1_tag_t){ .tag = SEQUENCE }),
      offset_data,
      b,
      pos - offset_data);
  b[pos - offset_data - offset2 - 1U] = encode_asn1_tag(((asn1_tag_t){ .tag = SEQUENCE }));
  uint32_t offset1 = 1U;
  uint32_t offset_tag_len = offset1 + offset2;
  return offset_tag_len + offset_data;
}

fwid_payload_t x509_get_fwid(FStar_Bytes_bytes fwid)
{
  return
    (
      (fwid_payload_t){ .fwid_hashAlg = OID_DIGEST_SHA256, .fwid_value = { .len = 32U, .s = fwid } }
    );
}

