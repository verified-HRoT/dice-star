/* 
  This file was generated by KreMLin <https://github.com/FStarLang/kremlin>
  KreMLin invocation: krml -no-prefix Minimal.Main Minimal.Main.fst -skip-compilation -tmpdir out -I /home/zhetao/Sources/hacl-star/specs -I /home/zhetao/Sources/hacl-star/specs/lemmas -I /home/zhetao/Sources/hacl-star/code/hash -I /home/zhetao/Sources/hacl-star/code/hkdf -I /home/zhetao/Sources/hacl-star/code/hmac -I /home/zhetao/Sources/hacl-star/code/curve25519 -I /home/zhetao/Sources/hacl-star/code/ed25519 -I /home/zhetao/Sources/hacl-star/lib -I /home/zhetao/Sources/hacl-star/providers/evercrypt -warn-error +11
  F* version: 953b2211
  KreMLin version: e324b7e6
 */

#include "kremlib.h"
#ifndef __WasmSupport_H
#define __WasmSupport_H




extern void WasmSupport_trap();

uint32_t WasmSupport_align_64(uint32_t x);

void WasmSupport_check_buffer_size(uint32_t s);

uint32_t WasmSupport_betole32(uint32_t x);

uint64_t WasmSupport_betole64(uint64_t x);

#define __WasmSupport_H_DEFINED
#endif
