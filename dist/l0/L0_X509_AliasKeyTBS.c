/* Automatically generated by the Kremlin tool */



#include "L0_X509_AliasKeyTBS.h"

#include "internal/ASN1_X509.h"

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
  uint32_t
  r =
    5U
    + len_of_x509_serialNumber(serialNumber)
    + 1U + len_of_asn1_length(5U) + 5U
    + len_of_aliasKeyTBS_issuer(i_common, i_org, i_country)
    + 34U
    + len_of_aliasKeyTBS_subject(s_common, s_org, s_country)
    + 44U
    + len_of_x509_extensions(len_of_aliasKeyTBS_extensions(version));
  return r;
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
    1U
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
  offset_data =
    serialize32_aliasKeyTBS_extensions_backwards(x.aliasKeyTBS_extensions,
      input,
      pos);
  uint32_t
  offset2 =
    serialize32_asn1_length_of_type_backwards(x509_extensions_outmost_explicit_tag,
      offset_data,
      input,
      pos - offset_data);
  input[pos - offset_data - offset2 - 1U] = encode_asn1_tag(x509_extensions_outmost_explicit_tag);
  uint32_t offset10 = 1U;
  uint32_t offset_tag_len = offset10 + offset2;
  uint32_t offset20 = offset_tag_len + offset_data;
  uint32_t
  offset21 =
    serialize32_subjectPublicKeyInfo_backwards(x.aliasKeyTBS_aliasKey_pub,
      input,
      pos - offset20);
  uint32_t
  offset22 =
    serialize32_aliasKeyTBS_subject_backwards(x.aliasKeyTBS_subject,
      input,
      pos - offset20 - offset21);
  uint32_t
  offset23 =
    serialize32_x509_validity_backwards(x.aliasKeyTBS_validity,
      input,
      pos - offset20 - offset21 - offset22);
  uint32_t
  offset24 =
    serialize32_aliasKeyTBS_issuer_backwards(x.aliasKeyTBS_issuer,
      input,
      pos - offset20 - offset21 - offset22 - offset23);
  uint32_t
  offset25 =
    serialize32_algorithmIdentifier_backwards(x.aliasKeyTBS_signatureAlg,
      input,
      pos - offset20 - offset21 - offset22 - offset23 - offset24);
  uint32_t
  offset26 =
    serialize32_x509_serialNumber_backwards(x.aliasKeyTBS_serialNumber,
      input,
      pos - offset20 - offset21 - offset22 - offset23 - offset24 - offset25);
  uint32_t
  offset1 =
    serialize32_x509_version_backwards(x.aliasKeyTBS_version,
      input,
      pos - offset20 - offset21 - offset22 - offset23 - offset24 - offset25 - offset26);
  uint32_t offset11 = offset1 + offset26;
  uint32_t offset12 = offset11 + offset25;
  uint32_t offset13 = offset12 + offset24;
  uint32_t offset14 = offset13 + offset23;
  uint32_t offset15 = offset14 + offset22;
  uint32_t offset16 = offset15 + offset21;
  return offset16 + offset20;
}

uint32_t serialize32_aliasKeyTBS_backwards(aliasKeyTBS_payload_t x, uint8_t *b, uint32_t pos)
{
  uint32_t offset_data = serialize32_aliasKeyTBS_payload_backwards(x, b, pos);
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
  aliasKeyTBS_issuer_payload_t issuer = x509_get_aliasKeyTBS_issuer(i_common, i_org, i_country);
  x509_validity_payload_t validity = { .notBefore = notBefore, .notAfter = notAfter };
  aliasKeyTBS_subject_payload_t
  subject = x509_get_aliasKeyTBS_subject(s_common, s_org, s_country);
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

