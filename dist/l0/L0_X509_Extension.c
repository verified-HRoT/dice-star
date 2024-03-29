/* Automatically generated by the Kremlin tool */



#include "L0_X509_Extension.h"

#include "internal/ASN1_X509.h"

uint32_t len_of_l0_extension_payload(int32_t version)
{
  return
    1U
    + len_of_asn1_length(len_of_asn1_integer(version))
    + len_of_asn1_integer(version)
    + 110U;
}

uint32_t len_of_l0_extension(int32_t version)
{
  return
    1U
    + len_of_asn1_length(len_of_l0_extension_payload(version))
    + len_of_l0_extension_payload(version);
}

uint32_t
serialize32_l0_extension_payload_backwards(
  l0_extension_payload_t x,
  uint8_t *input,
  uint32_t pos
)
{
  uint32_t offset_data = serialize32_compositeDeviceID_backwards(x.x509_extValue_l0, input, pos);
  uint32_t
  offset2 =
    serialize32_asn1_length_of_type_backwards(((asn1_tag_t){ .tag = OCTET_STRING }),
      offset_data,
      input,
      pos - offset_data);
  input[pos - offset_data - offset2 - 1U] =
    encode_asn1_tag(((asn1_tag_t){ .tag = OCTET_STRING }));
  uint32_t offset10 = 1U;
  uint32_t offset_tag_len = offset10 + offset2;
  uint32_t offset20 = offset_tag_len + offset_data;
  uint32_t
  offset21 = serialize32_asn1_boolean_TLV_backwards(x.x509_extCritical_l0, input, pos - offset20);
  uint32_t
  offset1 = serialize32_asn1_oid_TLV_backwards(x.x509_extID_l0, input, pos - offset20 - offset21);
  uint32_t offset11 = offset1 + offset21;
  return offset11 + offset20;
}

uint32_t serialize32_l0_extension_backwards(l0_extension_payload_t x, uint8_t *b, uint32_t pos)
{
  uint32_t offset_data = serialize32_compositeDeviceID_backwards(x.x509_extValue_l0, b, pos);
  uint32_t
  offset20 =
    serialize32_asn1_length_of_type_backwards(((asn1_tag_t){ .tag = OCTET_STRING }),
      offset_data,
      b,
      pos - offset_data);
  b[pos - offset_data - offset20 - 1U] = encode_asn1_tag(((asn1_tag_t){ .tag = OCTET_STRING }));
  uint32_t offset10 = 1U;
  uint32_t offset_tag_len = offset10 + offset20;
  uint32_t offset22 = offset_tag_len + offset_data;
  uint32_t
  offset21 = serialize32_asn1_boolean_TLV_backwards(x.x509_extCritical_l0, b, pos - offset22);
  uint32_t
  offset11 = serialize32_asn1_oid_TLV_backwards(x.x509_extID_l0, b, pos - offset22 - offset21);
  uint32_t offset12 = offset11 + offset21;
  uint32_t offset_data0 = offset12 + offset22;
  uint32_t
  offset2 =
    serialize32_asn1_length_of_type_backwards(((asn1_tag_t){ .tag = SEQUENCE }),
      offset_data0,
      b,
      pos - offset_data0);
  b[pos - offset_data0 - offset2 - 1U] = encode_asn1_tag(((asn1_tag_t){ .tag = SEQUENCE }));
  uint32_t offset1 = 1U;
  uint32_t offset_tag_len0 = offset1 + offset2;
  return offset_tag_len0 + offset_data0;
}

l0_extension_payload_t
x509_get_l0_extension(int32_t version, FStar_Bytes_bytes fwid, FStar_Bytes_bytes deviceIDPub)
{
  compositeDeviceID_payload_t
  compositeDeviceID = x509_get_compositeDeviceID(version, deviceIDPub, fwid);
  return
    (
      (l0_extension_payload_t){
        .x509_extID_l0 = OID_RIOT,
        .x509_extCritical_l0 = false,
        .x509_extValue_l0 = compositeDeviceID
      }
    );
}

