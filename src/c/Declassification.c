#include<stdio.h>

#include "RIoT_Declassify.h"

void RIoT_Declassify_declassify_secret_buffer (uint32_t len, uint8_t *src, uint8_t *dst)
{
  memcpy (dst, src, len);
}

void RIoT_Declassify_classify_public_buffer (uint32_t len, uint8_t *src, uint8_t *dst)
{
  memcpy (dst, src, len);
}
