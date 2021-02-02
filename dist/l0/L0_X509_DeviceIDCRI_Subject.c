/* Automatically generated by the Kremlin tool */



#include "L0_X509_DeviceIDCRI_Subject.h"

uint32_t
len_of_deviceIDCRI_subject_payload(
  character_string_t s_common,
  character_string_t s_org,
  character_string_t s_country
)
{
  return
    (uint32_t)1U
    +
      len_of_asn1_length((uint32_t)1U
        +
          len_of_asn1_length((uint32_t)1U
            + len_of_asn1_length((uint32_t)3U)
            + (uint32_t)3U
            +
              (uint32_t)1U
              + len_of_asn1_length(FStar_Pervasives_dfst__uint32_t_FStar_Bytes_bytes(s_common))
              + FStar_Pervasives_dfst__uint32_t_FStar_Bytes_bytes(s_common))
        +
          (uint32_t)1U
          + len_of_asn1_length((uint32_t)3U)
          + (uint32_t)3U
          +
            (uint32_t)1U
            + len_of_asn1_length(FStar_Pervasives_dfst__uint32_t_FStar_Bytes_bytes(s_common))
            + FStar_Pervasives_dfst__uint32_t_FStar_Bytes_bytes(s_common))
    +
      (uint32_t)1U
      +
        len_of_asn1_length((uint32_t)1U
          + len_of_asn1_length((uint32_t)3U)
          + (uint32_t)3U
          +
            (uint32_t)1U
            + len_of_asn1_length(FStar_Pervasives_dfst__uint32_t_FStar_Bytes_bytes(s_common))
            + FStar_Pervasives_dfst__uint32_t_FStar_Bytes_bytes(s_common))
      +
        (uint32_t)1U
        + len_of_asn1_length((uint32_t)3U)
        + (uint32_t)3U
        +
          (uint32_t)1U
          + len_of_asn1_length(FStar_Pervasives_dfst__uint32_t_FStar_Bytes_bytes(s_common))
          + FStar_Pervasives_dfst__uint32_t_FStar_Bytes_bytes(s_common)
    +
      (uint32_t)1U
      +
        len_of_asn1_length((uint32_t)1U
          +
            len_of_asn1_length((uint32_t)1U
              + len_of_asn1_length((uint32_t)3U)
              + (uint32_t)3U
              +
                (uint32_t)1U
                + len_of_asn1_length(FStar_Pervasives_dfst__uint32_t_FStar_Bytes_bytes(s_org))
                + FStar_Pervasives_dfst__uint32_t_FStar_Bytes_bytes(s_org))
          +
            (uint32_t)1U
            + len_of_asn1_length((uint32_t)3U)
            + (uint32_t)3U
            +
              (uint32_t)1U
              + len_of_asn1_length(FStar_Pervasives_dfst__uint32_t_FStar_Bytes_bytes(s_org))
              + FStar_Pervasives_dfst__uint32_t_FStar_Bytes_bytes(s_org))
      +
        (uint32_t)1U
        +
          len_of_asn1_length((uint32_t)1U
            + len_of_asn1_length((uint32_t)3U)
            + (uint32_t)3U
            +
              (uint32_t)1U
              + len_of_asn1_length(FStar_Pervasives_dfst__uint32_t_FStar_Bytes_bytes(s_org))
              + FStar_Pervasives_dfst__uint32_t_FStar_Bytes_bytes(s_org))
        +
          (uint32_t)1U
          + len_of_asn1_length((uint32_t)3U)
          + (uint32_t)3U
          +
            (uint32_t)1U
            + len_of_asn1_length(FStar_Pervasives_dfst__uint32_t_FStar_Bytes_bytes(s_org))
            + FStar_Pervasives_dfst__uint32_t_FStar_Bytes_bytes(s_org)
    +
      (uint32_t)1U
      +
        len_of_asn1_length((uint32_t)1U
          +
            len_of_asn1_length((uint32_t)1U
              + len_of_asn1_length((uint32_t)3U)
              + (uint32_t)3U
              +
                (uint32_t)1U
                + len_of_asn1_length(FStar_Pervasives_dfst__uint32_t_FStar_Bytes_bytes(s_country))
                + FStar_Pervasives_dfst__uint32_t_FStar_Bytes_bytes(s_country))
          +
            (uint32_t)1U
            + len_of_asn1_length((uint32_t)3U)
            + (uint32_t)3U
            +
              (uint32_t)1U
              + len_of_asn1_length(FStar_Pervasives_dfst__uint32_t_FStar_Bytes_bytes(s_country))
              + FStar_Pervasives_dfst__uint32_t_FStar_Bytes_bytes(s_country))
      +
        (uint32_t)1U
        +
          len_of_asn1_length((uint32_t)1U
            + len_of_asn1_length((uint32_t)3U)
            + (uint32_t)3U
            +
              (uint32_t)1U
              + len_of_asn1_length(FStar_Pervasives_dfst__uint32_t_FStar_Bytes_bytes(s_country))
              + FStar_Pervasives_dfst__uint32_t_FStar_Bytes_bytes(s_country))
        +
          (uint32_t)1U
          + len_of_asn1_length((uint32_t)3U)
          + (uint32_t)3U
          +
            (uint32_t)1U
            + len_of_asn1_length(FStar_Pervasives_dfst__uint32_t_FStar_Bytes_bytes(s_country))
            + FStar_Pervasives_dfst__uint32_t_FStar_Bytes_bytes(s_country);
}

uint32_t
len_of_deviceIDCRI_subject(
  character_string_t s_common,
  character_string_t s_org,
  character_string_t s_country
)
{
  return
    (uint32_t)1U
    + len_of_asn1_length(len_of_deviceIDCRI_subject_payload(s_common, s_org, s_country))
    + len_of_deviceIDCRI_subject_payload(s_common, s_org, s_country);
}

uint32_t
serialize32_deviceIDCRI_subject_payload_backwards(
  deviceIDCRI_subject_payload_t x,
  uint8_t *input,
  uint32_t pos
)
{
  uint32_t offset2 = serialize32_RDN_COUNTRY(x.deviceIDCRI_subject_Country, input, pos);
  uint32_t
  offset21 =
    serialize32_RDN_ORGANIZATION(x.deviceIDCRI_subject_Organization,
      input,
      pos - offset2);
  uint32_t
  offset1 =
    serialize32_RDN_COMMON_NAME(x.deviceIDCRI_subject_Common,
      input,
      pos - offset2 - offset21);
  uint32_t offset10 = offset1 + offset21;
  return offset10 + offset2;
}

uint32_t
serialize32_deviceIDCRI_subject_backwards(
  deviceIDCRI_subject_payload_t x,
  uint8_t *b,
  uint32_t pos
)
{
  uint32_t offset_data = serialize32_deviceIDCRI_subject_payload_backwards(x, b, pos);
  uint32_t
  offset2 =
    serialize32_asn1_length_of_type_backwards(((asn1_tag_t){ .tag = SEQUENCE }),
      offset_data,
      b,
      pos - offset_data);
  b[pos - offset_data - offset2 - (uint32_t)1U] =
    encode_asn1_tag(((asn1_tag_t){ .tag = SEQUENCE }));
  uint32_t offset1 = (uint32_t)1U;
  uint32_t offset_tag_len = offset1 + offset2;
  return offset_tag_len + offset_data;
}

deviceIDCRI_subject_payload_t
x509_get_deviceIDCRI_subject(
  character_string_t s_common,
  character_string_t s_org,
  character_string_t s_country
)
{
  x509_rdn_string_t rdn_common = { .fst = OID_AT_CN, .snd = s_common };
  x509_rdn_string_t rdn_org = { .fst = OID_AT_ORGANIZATION, .snd = s_org };
  x509_rdn_string_t rdn_country = { .fst = OID_AT_COUNTRY, .snd = s_country };
  return
    (
      (deviceIDCRI_subject_payload_t){
        .deviceIDCRI_subject_Common = rdn_common,
        .deviceIDCRI_subject_Organization = rdn_org,
        .deviceIDCRI_subject_Country = rdn_country
      }
    );
}
