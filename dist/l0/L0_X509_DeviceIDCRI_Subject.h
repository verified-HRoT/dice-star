/* Automatically generated by the Kremlin tool */



#ifndef __L0_X509_DeviceIDCRI_Subject_H
#define __L0_X509_DeviceIDCRI_Subject_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include "LowStar_Printf.h"
#include <string.h>


#include "ASN1_X509.h"

typedef struct deviceIDCRI_subject_payload_t_s
{
  x509_rdn_string_t deviceIDCRI_subject_Common;
  x509_rdn_string_t deviceIDCRI_subject_Organization;
  x509_rdn_string_t deviceIDCRI_subject_Country;
}
deviceIDCRI_subject_payload_t;

uint32_t
len_of_deviceIDCRI_subject_payload(
  Prims_dtuple2__uint32_t_FStar_Bytes_bytes s_common,
  Prims_dtuple2__uint32_t_FStar_Bytes_bytes s_org,
  Prims_dtuple2__uint32_t_FStar_Bytes_bytes s_country
);

typedef deviceIDCRI_subject_payload_t deviceIDCRI_subject_t;

uint32_t
len_of_deviceIDCRI_subject(
  Prims_dtuple2__uint32_t_FStar_Bytes_bytes s_common,
  Prims_dtuple2__uint32_t_FStar_Bytes_bytes s_org,
  Prims_dtuple2__uint32_t_FStar_Bytes_bytes s_country
);

uint32_t
serialize32_deviceIDCRI_subject_payload_backwards(
  deviceIDCRI_subject_payload_t x,
  uint8_t *input,
  uint32_t pos
);

uint32_t
serialize32_deviceIDCRI_subject_backwards(
  deviceIDCRI_subject_payload_t x,
  uint8_t *b,
  uint32_t pos
);

deviceIDCRI_subject_payload_t
x509_get_deviceIDCRI_subject(
  Prims_dtuple2__uint32_t_FStar_Bytes_bytes s_common,
  Prims_dtuple2__uint32_t_FStar_Bytes_bytes s_org,
  Prims_dtuple2__uint32_t_FStar_Bytes_bytes s_country
);

#if defined(__cplusplus)
}
#endif

#define __L0_X509_DeviceIDCRI_Subject_H_DEFINED
#endif
