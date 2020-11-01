/* Automatically generated by the Kremlin tool */



#include "L0_X509_AliasKeyTBS.h"

uint32_t
len_of_aliasKeyTBS_payload(
  octet_string_t serialNumber,
  character_string_t i_common,
  character_string_t i_org,
  character_string_t i_country,
  character_string_t s_common,
  character_string_t s_org,
  character_string_t s_country,
  int32_t version
)
{
  return
    (uint32_t)5U
    + len_of_x509_serialNumber(serialNumber)
    + (uint32_t)1U + len_of_asn1_length((uint32_t)5U) + (uint32_t)5U
    + len_of_aliasKeyTBS_issuer(i_common, i_org, i_country)
    + (uint32_t)34U
    + len_of_aliasKeyTBS_subject(s_common, s_org, s_country)
    + (uint32_t)44U
    + len_of_x509_extensions(len_of_aliasKeyTBS_extensions(version));
}

uint32_t
len_of_aliasKeyTBS(
  octet_string_t serialNumber,
  character_string_t i_common,
  character_string_t i_org,
  character_string_t i_country,
  character_string_t s_common,
  character_string_t s_org,
  character_string_t s_country,
  int32_t version
)
{
  return
    (uint32_t)1U
    +
      len_of_asn1_length(len_of_aliasKeyTBS_payload(serialNumber,
          i_common,
          i_org,
          i_country,
          s_common,
          s_org,
          s_country,
          version))
    +
      len_of_aliasKeyTBS_payload(serialNumber,
        i_common,
        i_org,
        i_country,
        s_common,
        s_org,
        s_country,
        version);
}

uint32_t
serialize32_aliasKeyTBS_payload_backwards(
  aliasKeyTBS_payload_t x,
  uint8_t *input,
  uint32_t pos
)
{
  uint32_t
  offset0 = serialize32_aliasKeyTBS_extensions_backwards(x.aliasKeyTBS_extensions, input, pos);
  uint32_t offset_data = offset0;
  uint32_t pos10 = pos - offset_data;
  uint32_t
  offset1 =
    serialize32_asn1_length_of_type_backwards(x509_extensions_outmost_explicit_tag,
      offset_data,
      input,
      pos10);
  uint32_t offset2 = offset1;
  uint32_t pos20 = pos10 - offset2;
  uint32_t offset3 = (uint32_t)1U;
  uint8_t content = encode_asn1_tag(x509_extensions_outmost_explicit_tag);
  input[pos20 - offset3] = content;
  uint32_t offset4 = offset3;
  uint32_t offset10 = offset4;
  uint32_t offset5 = offset10 + offset2;
  uint32_t offset_tag_len = offset5;
  uint32_t offset6 = offset_tag_len + offset_data;
  uint32_t offset20 = offset6;
  uint32_t pos1 = pos - offset20;
  uint32_t
  offset7 = serialize32_subjectPublicKeyInfo_backwards(x.aliasKeyTBS_aliasKey_pub, input, pos1);
  uint32_t offset21 = offset7;
  uint32_t pos2 = pos1 - offset21;
  uint32_t
  offset8 = serialize32_aliasKeyTBS_subject_backwards(x.aliasKeyTBS_subject, input, pos2);
  uint32_t offset22 = offset8;
  uint32_t pos3 = pos2 - offset22;
  uint32_t offset9 = serialize32_x509_validity_backwards(x.aliasKeyTBS_validity, input, pos3);
  uint32_t offset23 = offset9;
  uint32_t pos4 = pos3 - offset23;
  uint32_t
  offset11 = serialize32_aliasKeyTBS_issuer_backwards(x.aliasKeyTBS_issuer, input, pos4);
  uint32_t offset24 = offset11;
  uint32_t pos5 = pos4 - offset24;
  uint32_t
  offset12 = serialize32_algorithmIdentifier_backwards(x.aliasKeyTBS_signatureAlg, input, pos5);
  uint32_t offset25 = offset12;
  uint32_t pos6 = pos5 - offset25;
  uint32_t
  offset = serialize32_x509_serialNumber_backwards(x.aliasKeyTBS_serialNumber, input, pos6);
  uint32_t offset26 = offset;
  uint32_t pos7 = pos6 - offset26;
  uint32_t offset13 = serialize32_x509_version_backwards(x.aliasKeyTBS_version, input, pos7);
  uint32_t offset14 = offset13;
  uint32_t offset15 = offset14 + offset26;
  uint32_t offset16 = offset15;
  uint32_t offset17 = offset16 + offset25;
  uint32_t offset18 = offset17;
  uint32_t offset19 = offset18 + offset24;
  uint32_t offset110 = offset19;
  uint32_t offset27 = offset110 + offset23;
  uint32_t offset111 = offset27;
  uint32_t offset28 = offset111 + offset22;
  uint32_t offset112 = offset28;
  uint32_t offset29 = offset112 + offset21;
  uint32_t offset113 = offset29;
  return offset113 + offset20;
}

uint32_t serialize32_aliasKeyTBS_backwards(aliasKeyTBS_payload_t x, uint8_t *b, uint32_t pos)
{
  uint32_t offset0 = serialize32_aliasKeyTBS_payload_backwards(x, b, pos);
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

aliasKeyTBS_payload_t
x509_get_AliasKeyTBS(
  int32_t crt_version,
  octet_string_t serialNumber,
  character_string_t i_common,
  character_string_t i_org,
  character_string_t i_country,
  FStar_Bytes_bytes notBefore,
  FStar_Bytes_bytes notAfter,
  character_string_t s_common,
  character_string_t s_org,
  character_string_t s_country,
  int32_t ku,
  octet_string_t keyID,
  int32_t version,
  FStar_Bytes_bytes fwid,
  FStar_Bytes_bytes deviceIDPub,
  FStar_Bytes_bytes aliasKeyPub
)
{
  oid_t signatureAlg = OID_ED25519;
  aliasKeyTBS_issuer_payload_t
  issuer =
    x509_get_aliasKeyTBS_issuer(FStar_Pervasives_dfst__uint32_t_FStar_Bytes_bytes(i_common),
      FStar_Pervasives_dsnd__uint32_t_FStar_Bytes_bytes(i_common),
      FStar_Pervasives_dfst__uint32_t_FStar_Bytes_bytes(i_org),
      FStar_Pervasives_dsnd__uint32_t_FStar_Bytes_bytes(i_org),
      FStar_Pervasives_dfst__uint32_t_FStar_Bytes_bytes(i_country),
      FStar_Pervasives_dsnd__uint32_t_FStar_Bytes_bytes(i_country));
  x509_validity_payload_t validity = { .notBefore = notBefore, .notAfter = notAfter };
  aliasKeyTBS_subject_payload_t
  subject =
    x509_get_aliasKeyTBS_subject(FStar_Pervasives_dfst__uint32_t_FStar_Bytes_bytes(s_common),
      FStar_Pervasives_dsnd__uint32_t_FStar_Bytes_bytes(s_common),
      FStar_Pervasives_dfst__uint32_t_FStar_Bytes_bytes(s_org),
      FStar_Pervasives_dsnd__uint32_t_FStar_Bytes_bytes(s_org),
      FStar_Pervasives_dfst__uint32_t_FStar_Bytes_bytes(s_country),
      FStar_Pervasives_dsnd__uint32_t_FStar_Bytes_bytes(s_country));
  subjectPublicKeyInfo_payload_t aliasKeyPubInfo = x509_get_subjectPublicKeyInfo(aliasKeyPub);
  aliasKeyTBS_extensions_payload_t
  extensions = x509_get_aliasKeyTBS_extensions(ku, keyID, version, fwid, deviceIDPub);
  return
    (
      (aliasKeyTBS_payload_t){
        .aliasKeyTBS_version = crt_version,
        .aliasKeyTBS_serialNumber = serialNumber,
        .aliasKeyTBS_signatureAlg = signatureAlg,
        .aliasKeyTBS_issuer = issuer,
        .aliasKeyTBS_validity = validity,
        .aliasKeyTBS_subject = subject,
        .aliasKeyTBS_aliasKey_pub = aliasKeyPubInfo,
        .aliasKeyTBS_extensions = extensions
      }
    );
}

