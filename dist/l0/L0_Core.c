/* Automatically generated by the Kremlin tool */



#include "L0_Core.h"

void
l0_aux(
  uint8_t *cdi,
  uint8_t *fwid,
  uint32_t deviceID_label_len,
  uint8_t *deviceID_label,
  uint32_t aliasKey_label_len,
  uint8_t *aliasKey_label,
  deviceIDCSR_ingredients_t deviceIDCSR_ingredients,
  aliasKeyCRT_ingredients_t aliasKeyCRT_ingredients,
  uint8_t *deviceID_pub,
  uint8_t *aliasKey_pub,
  uint8_t *aliasKey_priv,
  uint32_t deviceIDCSR_len,
  uint8_t *deviceIDCSR_buf,
  uint32_t aliasKeyCRT_len,
  uint8_t *aliasKeyCRT_buf
)
{
  uint8_t deviceID_priv[32U];
  memset(deviceID_priv, 0U, (uint32_t)32U * sizeof (uint8_t));
  uint8_t authKeyID[20U];
  memset(authKeyID, 0U, (uint32_t)20U * sizeof (uint8_t));
  uint8_t deviceID_pub_sec[32U];
  memset(deviceID_pub_sec, 0U, (uint32_t)32U * sizeof (uint8_t));
  LowStar_Printf_print_string("Deriving DeviceID\n");
  derive_DeviceID(deviceID_pub, deviceID_priv, cdi, deviceID_label_len, deviceID_label);
  LowStar_Printf_print_string("Deriving AliasKey\n");
  derive_AliasKey(aliasKey_pub, aliasKey_priv, cdi, fwid, aliasKey_label_len, aliasKey_label);
  classify_public_buffer((uint32_t)32U, deviceID_pub, deviceID_pub_sec);
  derive_authKeyID(authKeyID, deviceID_pub_sec);
  uint32_t
  deviceIDCRI_len =
    len_of_deviceIDCRI(deviceIDCSR_ingredients.deviceIDCSR_version,
      deviceIDCSR_ingredients.deviceIDCSR_s_common,
      deviceIDCSR_ingredients.deviceIDCSR_s_org,
      deviceIDCSR_ingredients.deviceIDCSR_s_country);
  KRML_CHECK_SIZE(sizeof (uint8_t), deviceIDCRI_len);
  uint8_t deviceIDCRI_buf[deviceIDCRI_len];
  memset(deviceIDCRI_buf, 0U, deviceIDCRI_len * sizeof (uint8_t));
  LowStar_Printf_print_string("Creating DeviceID Certificate Signing Request Information\n");
  create_deviceIDCRI(deviceIDCSR_ingredients.deviceIDCSR_version,
    deviceIDCSR_ingredients.deviceIDCSR_s_common,
    deviceIDCSR_ingredients.deviceIDCSR_s_org,
    deviceIDCSR_ingredients.deviceIDCSR_s_country,
    deviceIDCSR_ingredients.deviceIDCSR_ku,
    deviceID_pub,
    deviceIDCRI_len,
    deviceIDCRI_buf);
  LowStar_Printf_print_string("Signing and finalizing DeviceID Certificate Signing Request\n");
  sign_and_finalize_deviceIDCSR(deviceID_priv,
    deviceIDCRI_len,
    deviceIDCRI_buf,
    deviceIDCSR_len,
    deviceIDCSR_buf);
  uint32_t
  aliasKeyTBS_len =
    len_of_aliasKeyTBS(aliasKeyCRT_ingredients.aliasKeyCrt_serialNumber,
      aliasKeyCRT_ingredients.aliasKeyCrt_i_common,
      aliasKeyCRT_ingredients.aliasKeyCrt_i_org,
      aliasKeyCRT_ingredients.aliasKeyCrt_i_country,
      aliasKeyCRT_ingredients.aliasKeyCrt_s_common,
      aliasKeyCRT_ingredients.aliasKeyCrt_s_org,
      aliasKeyCRT_ingredients.aliasKeyCrt_s_country,
      aliasKeyCRT_ingredients.aliasKeyCrt_l0_version);
  KRML_CHECK_SIZE(sizeof (uint8_t), aliasKeyTBS_len);
  uint8_t aliasKeyTBS_buf[aliasKeyTBS_len];
  memset(aliasKeyTBS_buf, 0U, aliasKeyTBS_len * sizeof (uint8_t));
  LowStar_Printf_print_string("Creating AliasKey Certificate TBS\n");
  create_aliasKeyTBS(aliasKeyCRT_ingredients.aliasKeyCrt_version,
    aliasKeyCRT_ingredients.aliasKeyCrt_serialNumber,
    aliasKeyCRT_ingredients.aliasKeyCrt_i_common,
    aliasKeyCRT_ingredients.aliasKeyCrt_i_org,
    aliasKeyCRT_ingredients.aliasKeyCrt_i_country,
    aliasKeyCRT_ingredients.aliasKeyCrt_notBefore,
    aliasKeyCRT_ingredients.aliasKeyCrt_notAfter,
    aliasKeyCRT_ingredients.aliasKeyCrt_s_common,
    aliasKeyCRT_ingredients.aliasKeyCrt_s_org,
    aliasKeyCRT_ingredients.aliasKeyCrt_s_country,
    fwid,
    aliasKeyCRT_ingredients.aliasKeyCrt_ku,
    authKeyID,
    aliasKeyCRT_ingredients.aliasKeyCrt_l0_version,
    deviceID_pub,
    aliasKey_pub,
    aliasKeyTBS_len,
    aliasKeyTBS_buf);
  LowStar_Printf_print_string("Signing and finalizing AliasKey Certificate\n");
  sign_and_finalize_aliasKeyCRT(deviceID_priv,
    aliasKeyTBS_len,
    aliasKeyTBS_buf,
    aliasKeyCRT_len,
    aliasKeyCRT_buf);
}

void
l0(
  uint8_t *cdi,
  uint8_t *fwid,
  uint32_t deviceID_label_len,
  uint8_t *deviceID_label,
  uint32_t aliasKey_label_len,
  uint8_t *aliasKey_label,
  deviceIDCSR_ingredients_t deviceIDCSR_ingredients,
  aliasKeyCRT_ingredients_t aliasKeyCRT_ingredients,
  uint8_t *deviceID_pub,
  uint8_t *aliasKey_pub,
  uint8_t *aliasKey_priv,
  uint32_t deviceIDCSR_len,
  uint8_t *deviceIDCSR_buf,
  uint32_t aliasKeyCRT_len,
  uint8_t *aliasKeyCRT_buf
)
{
  KRML_CHECK_SIZE(sizeof (uint8_t), deviceID_label_len);
  uint8_t dk_label[deviceID_label_len];
  memset(dk_label, 0U, deviceID_label_len * sizeof (uint8_t));
  KRML_CHECK_SIZE(sizeof (uint8_t), aliasKey_label_len);
  uint8_t ak_label[aliasKey_label_len];
  memset(ak_label, 0U, aliasKey_label_len * sizeof (uint8_t));
  classify_public_buffer(deviceID_label_len, deviceID_label, dk_label);
  classify_public_buffer(aliasKey_label_len, aliasKey_label, ak_label);
  l0_aux(cdi,
    fwid,
    deviceID_label_len,
    dk_label,
    aliasKey_label_len,
    ak_label,
    deviceIDCSR_ingredients,
    aliasKeyCRT_ingredients,
    deviceID_pub,
    aliasKey_pub,
    aliasKey_priv,
    deviceIDCSR_len,
    deviceIDCSR_buf,
    aliasKeyCRT_len,
    aliasKeyCRT_buf);
}
