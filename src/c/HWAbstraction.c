#include "HWAbstraction.h"

uint32_t uds_len = 32;

HWState_state st = {
		    (uint8_t *) 1,        /* cdi */
		    1U,                   /* l0 image header size */
		    (uint8_t *) 1,        /* l0 image header */
		    (uint8_t *) 1,        /* l0 image header signature */
		    1U,                   /* l0 binary size */
		    (uint8_t *) 1,        /* l0 binary */
		    (uint8_t *) 1,        /* l0 binary hash */
		    (uint8_t *) 1 };      /* l0 image authentication key */

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
