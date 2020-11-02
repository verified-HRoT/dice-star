/* Automatically generated by the Kremlin tool */



#include "L0_Impl_Certificate.h"

void
create_aliasKeyTBS(
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
  uint8_t *fwid,
  int32_t ku,
  uint8_t *keyID,
  int32_t l0_version,
  uint8_t *deviceID_pub,
  uint8_t *aliasKey_pub,
  uint32_t aliasKeyTBS_len,
  uint8_t *aliasKeyTBS_buf
)
{
  FStar_Bytes_bytes fwid_pub32 = FStar_Bytes_of_buffer((uint32_t)32U, (uint8_t *)fwid);
  FStar_Bytes_bytes
  deviceID_pub32 = FStar_Bytes_of_buffer((uint32_t)32U, (uint8_t *)deviceID_pub);
  FStar_Bytes_bytes
  aliasKey_pub32 = FStar_Bytes_of_buffer((uint32_t)32U, (uint8_t *)aliasKey_pub);
  FStar_Bytes_bytes keyID_pub32 = FStar_Bytes_of_buffer((uint32_t)20U, (uint8_t *)keyID);
  aliasKeyTBS_bytes
  b =
    {
      .fwid_pub32 = fwid_pub32,
      .keyID_pub32 = keyID_pub32,
      .deviceID_pub32 = deviceID_pub32,
      .aliasKey_pub32 = aliasKey_pub32
    };
  octet_string_t keyID_string = { .len = (uint32_t)20U, .s = b.keyID_pub32 };
  LowStar_Printf_print_string("Creating AliasKey Certificate TBS Message\n");
  aliasKeyTBS_payload_t
  aliasKeyTBS =
    x509_get_AliasKeyTBS(crt_version,
      serialNumber,
      i_common,
      i_org,
      i_country,
      notBefore,
      notAfter,
      s_common,
      s_org,
      s_country,
      ku,
      keyID_string,
      l0_version,
      b.fwid_pub32,
      b.deviceID_pub32,
      b.aliasKey_pub32);
  LowStar_Printf_print_string("Serializing AliasKey Certificate TBS\n");
  uint32_t
  _offset =
    serialize32_aliasKeyTBS_backwards(aliasKeyTBS,
      (uint8_t *)aliasKeyTBS_buf,
      aliasKeyTBS_len);
}

void
sign_and_finalize_aliasKeyCRT(
  uint8_t *deviceID_priv,
  uint32_t aliasKeyTBS_len,
  uint8_t *aliasKeyTBS_buf,
  uint32_t aliasKeyCRT_len,
  uint8_t *aliasKeyCRT_buf
)
{
  KRML_CHECK_SIZE(sizeof (uint8_t), aliasKeyTBS_len);
  uint8_t aliasKeyTBS_buf_sec[aliasKeyTBS_len];
  memset(aliasKeyTBS_buf_sec, 0U, aliasKeyTBS_len * sizeof (uint8_t));
  classify_public_buffer(aliasKeyTBS_len, aliasKeyTBS_buf, aliasKeyTBS_buf_sec);
  uint8_t aliasKeyTBS_sig_sec[64U];
  memset(aliasKeyTBS_sig_sec, 0U, (uint32_t)64U * sizeof (uint8_t));
  Hacl_Ed25519_sign(aliasKeyTBS_sig_sec, deviceID_priv, aliasKeyTBS_len, aliasKeyTBS_buf_sec);
  uint8_t aliasKeyTBS_sig[64U];
  memset(aliasKeyTBS_sig, 0U, (uint32_t)64U * sizeof (uint8_t));
  declassify_secret_buffer((uint32_t)64U, aliasKeyTBS_sig_sec, aliasKeyTBS_sig);
  FStar_Bytes_bytes
  aliasKeyTBS_buf32 = FStar_Bytes_of_buffer(aliasKeyTBS_len, (uint8_t *)aliasKeyTBS_buf);
  FStar_Bytes_bytes
  aliasKeyTBS_sig32 = FStar_Bytes_of_buffer((uint32_t)64U, (uint8_t *)aliasKeyTBS_sig);
  LowStar_Printf_print_string("Creating AliasKey Certificate CRT message\n");
  aliasKeyCRT_payload_t
  aliasKeyCRT = x509_get_AliasKeyCRT(aliasKeyTBS_len, aliasKeyTBS_buf32, aliasKeyTBS_sig32);
  LowStar_Printf_print_string("Serializing AliasKey Certificate CRT\n");
  uint32_t
  _offset =
    serialize32_aliasKeyCRT_backwards(aliasKeyTBS_len,
      aliasKeyCRT,
      (uint8_t *)aliasKeyCRT_buf,
      aliasKeyCRT_len);
}

void
create_deviceIDCRI(
  int32_t csr_version,
  character_string_t s_common,
  character_string_t s_org,
  character_string_t s_country,
  int32_t ku,
  uint8_t *deviceID_pub,
  uint32_t deviceIDCRI_len,
  uint8_t *deviceIDCRI_buf
)
{
  FStar_Bytes_bytes
  deviceID_pub32 = FStar_Bytes_of_buffer((uint32_t)32U, (uint8_t *)deviceID_pub);
  LowStar_Printf_print_string("Creating AliasKey Certificate TBS Message\n");
  deviceIDCRI_payload_t
  deviceIDCRI = x509_get_deviceIDCRI(csr_version, s_common, s_org, s_country, ku, deviceID_pub32);
  LowStar_Printf_print_string("Serializing AliasKey Certificate TBS\n");
  uint32_t
  offset =
    serialize32_deviceIDCRI_backwards(deviceIDCRI,
      (uint8_t *)deviceIDCRI_buf,
      deviceIDCRI_len);
}

void
sign_and_finalize_deviceIDCSR(
  uint8_t *deviceID_priv,
  uint32_t deviceIDCRI_len,
  uint8_t *deviceIDCRI_buf,
  uint32_t deviceIDCSR_len,
  uint8_t *deviceIDCSR_buf
)
{
  KRML_CHECK_SIZE(sizeof (uint8_t), deviceIDCRI_len);
  uint8_t deviceIDCRI_buf_sec[deviceIDCRI_len];
  memset(deviceIDCRI_buf_sec, 0U, deviceIDCRI_len * sizeof (uint8_t));
  classify_public_buffer(deviceIDCRI_len, deviceIDCRI_buf, deviceIDCRI_buf_sec);
  uint8_t deviceIDCRI_sig_sec[64U];
  memset(deviceIDCRI_sig_sec, 0U, (uint32_t)64U * sizeof (uint8_t));
  Hacl_Ed25519_sign(deviceIDCRI_sig_sec, deviceID_priv, deviceIDCRI_len, deviceIDCRI_buf_sec);
  uint8_t deviceIDCRI_sig[64U];
  memset(deviceIDCRI_sig, 0U, (uint32_t)64U * sizeof (uint8_t));
  declassify_secret_buffer((uint32_t)64U, deviceIDCRI_sig_sec, deviceIDCRI_sig);
  FStar_Bytes_bytes
  deviceIDCRI_buf32 = FStar_Bytes_of_buffer(deviceIDCRI_len, (uint8_t *)deviceIDCRI_buf);
  FStar_Bytes_bytes
  deviceIDCRI_sig32 = FStar_Bytes_of_buffer((uint32_t)64U, (uint8_t *)deviceIDCRI_sig);
  LowStar_Printf_print_string("Creating AliasKey Certificate CRT message\n");
  deviceIDCSR_payload_t
  deviceIDCSR = x509_get_deviceIDCSR(deviceIDCRI_len, deviceIDCRI_buf32, deviceIDCRI_sig32);
  LowStar_Printf_print_string("Serializing AliasKey Certificate CRT\n");
  uint32_t
  offset =
    serialize32_deviceIDCSR_backwards(deviceIDCRI_len,
      deviceIDCSR,
      (uint8_t *)deviceIDCSR_buf,
      deviceIDCSR_len);
}

