/* Automatically generated by the Kremlin tool */



#include "L0_X509_AliasKeyTBS_Extensions.h"

uint32_t len_of_aliasKeyTBS_extensions_payload(int32_t version)
{
  oid_t value0 = OID_BASIC_CONSTRAINTS;
  uint32_t value_len0 = len_of_oid(value0);
  uint32_t len_len0 = len_of_asn1_length(value_len0);
  uint32_t tag_len0 = (uint32_t)1U;
  uint32_t value_len1 = (uint32_t)1U;
  uint32_t len_len1 = len_of_asn1_length(value_len1);
  uint32_t tag_len1 = (uint32_t)1U;
  uint32_t value_len2 = (uint32_t)1U;
  uint32_t len_len2 = len_of_asn1_length(value_len2);
  uint32_t tag_len2 = (uint32_t)1U;
  uint32_t value_len3 = (uint32_t)1U;
  uint32_t len_len3 = len_of_asn1_length(value_len3);
  uint32_t tag_len3 = (uint32_t)1U;
  uint32_t value_len4 = (uint32_t)1U;
  uint32_t len_len4 = len_of_asn1_length(value_len4);
  uint32_t tag_len4 = (uint32_t)1U;
  uint32_t value_len5 = (uint32_t)1U;
  uint32_t len_len5 = len_of_asn1_length(value_len5);
  uint32_t tag_len5 = (uint32_t)1U;
  oid_t value = OID_BASIC_CONSTRAINTS;
  uint32_t value_len6 = len_of_oid(value);
  uint32_t len_len6 = len_of_asn1_length(value_len6);
  uint32_t tag_len6 = (uint32_t)1U;
  uint32_t value_len7 = (uint32_t)1U;
  uint32_t len_len7 = len_of_asn1_length(value_len7);
  uint32_t tag_len7 = (uint32_t)1U;
  uint32_t value_len8 = (uint32_t)1U;
  uint32_t len_len8 = len_of_asn1_length(value_len8);
  uint32_t tag_len8 = (uint32_t)1U;
  uint32_t value_len9 = (uint32_t)1U;
  uint32_t len_len9 = len_of_asn1_length(value_len9);
  uint32_t tag_len9 = (uint32_t)1U;
  uint32_t value_len10 = (uint32_t)1U;
  uint32_t len_len10 = len_of_asn1_length(value_len10);
  uint32_t tag_len10 = (uint32_t)1U;
  uint32_t value_len = (uint32_t)1U;
  uint32_t len_len = len_of_asn1_length(value_len);
  uint32_t tag_len = (uint32_t)1U;
  return
    (uint32_t)38U
    +
      (uint32_t)1U
      +
        len_of_asn1_length(tag_len0
          + len_len0
          + value_len0
          + tag_len1 + len_len1 + value_len1
          +
            (uint32_t)1U
            +
              len_of_asn1_length((uint32_t)1U
                + len_of_asn1_length(tag_len2 + len_len2 + value_len2)
                + tag_len3 + len_len3 + value_len3)
            +
              (uint32_t)1U
              + len_of_asn1_length(tag_len4 + len_len4 + value_len4)
              + tag_len5 + len_len5 + value_len5)
      +
        tag_len6
        + len_len6
        + value_len6
        + tag_len7 + len_len7 + value_len7
        +
          (uint32_t)1U
          +
            len_of_asn1_length((uint32_t)1U
              + len_of_asn1_length(tag_len8 + len_len8 + value_len8)
              + tag_len9 + len_len9 + value_len9)
          +
            (uint32_t)1U
            + len_of_asn1_length(tag_len10 + len_len10 + value_len10)
            + tag_len + len_len + value_len
    + (uint32_t)36U
    + len_of_l0_extension(version);
}

uint32_t len_of_aliasKeyTBS_extensions(int32_t version)
{
  return
    (uint32_t)1U
    + len_of_asn1_length(len_of_aliasKeyTBS_extensions_payload(version))
    + len_of_aliasKeyTBS_extensions_payload(version);
}

uint32_t
serialize32_aliasKeyTBS_extensions_payload_backwards(
  aliasKeyTBS_extensions_payload_t x,
  uint8_t *input,
  uint32_t pos
)
{
  uint32_t offset0 = serialize32_l0_extension_backwards(x.aliasKeyTBS_extensions_l0, input, pos);
  uint32_t offset2 = offset0;
  uint32_t pos1 = pos - offset2;
  uint32_t
  offset1 =
    serialize32_aliasKeyTBS_extensions_authKeyID_backwards(x.aliasKeyTBS_extensions_authKeyID,
      input,
      pos1);
  uint32_t offset21 = offset1;
  uint32_t pos2 = pos1 - offset21;
  uint32_t
  offset3 =
    serialize32_aliasKeyTBS_extensions_basicConstraints_backwards(x.aliasKeyTBS_extensions_basicConstraints,
      input,
      pos2);
  uint32_t offset22 = offset3;
  uint32_t pos3 = pos2 - offset22;
  uint32_t
  offset =
    serialize32_aliasKeyTBS_extensions_extendedKeyUsage_backwards(x.aliasKeyTBS_extensions_extendedKeyUsage,
      input,
      pos3);
  uint32_t offset23 = offset;
  uint32_t pos4 = pos3 - offset23;
  uint32_t
  offset4 = serialize32_x509_key_usage_backwards(x.aliasKeyTBS_extensions_key_usage, input, pos4);
  uint32_t offset10 = offset4;
  uint32_t offset5 = offset10 + offset23;
  uint32_t offset11 = offset5;
  uint32_t offset6 = offset11 + offset22;
  uint32_t offset12 = offset6;
  uint32_t offset7 = offset12 + offset21;
  uint32_t offset13 = offset7;
  return offset13 + offset2;
}

uint32_t
serialize32_aliasKeyTBS_extensions_backwards(
  aliasKeyTBS_extensions_payload_t x,
  uint8_t *b,
  uint32_t pos
)
{
  uint32_t offset0 = serialize32_aliasKeyTBS_extensions_payload_backwards(x, b, pos);
  uint32_t offset_data = offset0;
  uint32_t pos1 = pos - offset_data;
  uint32_t
  offset1 =
    serialize32_asn1_length_of_type_backwards(((asn1_tag_t){ .tag = SEQUENCE }),
      offset_data,
      b,
      pos1);
  uint32_t offset2 = offset1;
  uint32_t pos2 = pos1 - offset2;
  uint32_t offset = (uint32_t)1U;
  uint8_t content = encode_asn1_tag(((asn1_tag_t){ .tag = SEQUENCE }));
  b[pos2 - offset] = content;
  uint32_t offset3 = offset;
  uint32_t offset10 = offset3;
  uint32_t offset4 = offset10 + offset2;
  uint32_t offset_tag_len = offset4;
  return offset_tag_len + offset_data;
}

aliasKeyTBS_extensions_payload_t
x509_get_aliasKeyTBS_extensions(
  int32_t ku,
  octet_string_t keyID,
  int32_t version,
  FStar_Bytes_bytes fwid,
  FStar_Bytes_bytes deviceIDPub
)
{
  key_usage_t key_usage = { .fst = OID_KEY_USAGE, .snd = ku };
  aliasKeyTBS_extensions_extendedKeyUsage_t
  extendedKeyUsage = x509_get_aliasKeyTBS_extensions_extendedKeyUsage(true);
  aliasKeyTBS_extensions_basicConstraints_t
  basicConstraints = x509_get_aliasKeyTBS_extensions_basicConstraints(false);
  aliasKeyTBS_extensions_authKeyID_t
  authKeyID = x509_get_aliasKeyTBS_extensions_authKeyID(true, keyID);
  l0_extension_payload_t l0_extension = x509_get_l0_extension(version, fwid, deviceIDPub);
  return
    (
      (aliasKeyTBS_extensions_payload_t){
        .aliasKeyTBS_extensions_key_usage = key_usage,
        .aliasKeyTBS_extensions_extendedKeyUsage = extendedKeyUsage,
        .aliasKeyTBS_extensions_basicConstraints = basicConstraints,
        .aliasKeyTBS_extensions_authKeyID = authKeyID,
        .aliasKeyTBS_extensions_l0 = l0_extension
      }
    );
}
