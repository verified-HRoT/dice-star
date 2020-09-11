#include "HWAbstraction.h"

uint32_t uds_len = 32;

uint8_t *b = (uint8_t *) 1;

HWState_state st = {
		    (uint8_t *) 1,
		    1U,
		    (uint8_t *) 1,
		    (uint8_t *) 1,
		    1U,
		    (uint8_t *) 1,
		    (uint8_t *) 1,
		    (uint8_t *) 1 };

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
