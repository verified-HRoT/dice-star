#include "HWAbstraction.h"

uint32_t uds_len = 32;

uint8_t *get_uds(state s)
{
  return s.uds;
}

uint8_t *get_cdi(state s)
{
  return s.cdi;
}

riot_header_t get_riot_header(state s)
{
  return s.riot_header;
}

state initialize()
{
  uint8_t *uds = (uint8_t *) malloc(32U);
  uint8_t *cdi = (uint8_t *) malloc(32U);

  uint32_t riot_size = 32U;
  uint8_t *riot_binary = (uint8_t *) malloc(32U);
  uint8_t *sig = (uint8_t *) malloc(64U);
  uint8_t *pubkey = (uint8_t *) malloc(32U);

  return ((state) { uds, cdi, (riot_header_t) { riot_size, sig, riot_binary, pubkey } });
}

void unset_uds(state s)
{
}

void disable_uds(state s)
{
}
