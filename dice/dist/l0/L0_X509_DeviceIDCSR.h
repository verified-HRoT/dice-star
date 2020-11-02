/* Automatically generated by the Kremlin tool */



#ifndef __L0_X509_DeviceIDCSR_H
#define __L0_X509_DeviceIDCSR_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include "LowStar_Printf.h"
#include <string.h>


#include "ASN1_X509.h"

typedef struct deviceIDCSR_payload_t_s
{
  FStar_Bytes_bytes deviceIDCSR_cri;
  oid_t deviceIDCSR_sig_alg;
  bit_string_t deviceIDCSR_sig;
}
deviceIDCSR_payload_t;

uint32_t len_of_deviceIDCSR_payload(uint32_t cri_len);

uint32_t len_of_deviceIDCSR(uint32_t cri_len);

uint32_t
serialize32_deviceIDCSR_payload_backwards(
  uint32_t cri_len,
  deviceIDCSR_payload_t x,
  uint8_t *input,
  uint32_t pos
);

uint32_t
serialize32_deviceIDCSR_backwards(
  uint32_t cri_len,
  deviceIDCSR_payload_t x,
  uint8_t *b,
  uint32_t pos
);

deviceIDCSR_payload_t
x509_get_deviceIDCSR(
  uint32_t cri_len,
  FStar_Bytes_bytes deviceIDCSR_cri,
  FStar_Bytes_bytes signature32
);

#if defined(__cplusplus)
}
#endif

#define __L0_X509_DeviceIDCSR_H_DEFINED
#endif