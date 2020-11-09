#include "HWAbstraction.h"

uint32_t uds_len = 32;

HWState_state st ()
{
  HWState_l0_image_t img = { 1U, (uint8_t *) 1,
			     (uint8_t *) 1, 1U, (uint8_t *) 1,        
			     (uint8_t *) 1, (uint8_t *) 1 };
  HWState_state sta = { (uint8_t *) 1, img };
  return sta;
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

void zeroize (uint32_t len, uint8_t* buf) {
  return;
}
