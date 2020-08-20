#include "HWAbstraction.h"

uint32_t uds_len = 32;

image_t get_riot_image () {
  uint32_t header_size = 100U;
  uint8_t *image_header = (uint8_t *) malloc(header_size);
  uint8_t *image_hash = (uint8_t *) malloc(32U);
  uint8_t *header_sig = (uint8_t *) malloc(32U);
  uint32_t image_size = 100U;
  uint8_t *image_base = (uint8_t *) malloc(image_size);
  return ( (image_t) { header_size, image_header, image_hash, header_sig, image_size, image_base } );
}

void read_uds(uint8_t *uds) {
  return;
}

void platform_zeroize_stack () {
  return;
}

void disable_uds () {
  return;
}

void platform_zeroize (uint32_t len, uint8_t* buf) {
  return;
}
