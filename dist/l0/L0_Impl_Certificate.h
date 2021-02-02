/* Automatically generated by the Kremlin tool */



#ifndef __L0_Impl_Certificate_H
#define __L0_Impl_Certificate_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include "LowStar_Printf.h"
#include <string.h>


#include "L0_X509_AliasKeyTBS.h"
#include "ASN1_X509.h"
#include "L0_Declassify.h"
#include "L0_X509_DeviceIDCSR.h"
#include "L0_X509_AliasKeyCRT.h"
#include "L0_X509_DeviceIDCRI.h"
#include "Hacl_Lib.h"

typedef struct aliasKeyTBS_bytes_s
{
  FStar_Bytes_bytes fwid_pub32;
  FStar_Bytes_bytes keyID_pub32;
  FStar_Bytes_bytes deviceID_pub32;
  FStar_Bytes_bytes aliasKey_pub32;
}
aliasKeyTBS_bytes;

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
);

void
sign_and_finalize_aliasKeyCRT(
  uint8_t *deviceID_priv,
  uint32_t aliasKeyTBS_len,
  uint8_t *aliasKeyTBS_buf,
  uint32_t aliasKeyCRT_len,
  uint8_t *aliasKeyCRT_buf
);

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
);

void
sign_and_finalize_deviceIDCSR(
  uint8_t *deviceID_priv,
  uint32_t deviceIDCRI_len,
  uint8_t *deviceIDCRI_buf,
  uint32_t deviceIDCSR_len,
  uint8_t *deviceIDCSR_buf
);

#if defined(__cplusplus)
}
#endif

#define __L0_Impl_Certificate_H_DEFINED
#endif