/* 
  This file was generated by KreMLin <https://github.com/FStarLang/kremlin>
  KreMLin invocation: krml ./src/Minimal.DICE.fst -cc clang -no-prefix Hacl.Frodo.Random -bundle Hacl.Spec.*,Spec.*[rename=Hacl_Spec] -bundle Lib.*[rename=Hacl_Lib] -drop Lib.IntVector.Intrinsics -fparentheses -fno-shadow -fcurly-braces -bundle LowStar.* -bundle Prims,C.Failure,C,C.String,C.Loops,Spec.Loops,C.Endianness,FStar.*[rename=Hacl_Kremlib] -bundle Meta.* -minimal -add-include "kremlin/internal/types.h" -add-include "kremlin/lowstar_endianness.h" -add-include <string.h> -drop WasmSupport -tmpdir ./out -I ./src -add-include "kremlin/internal/compat.h" -I /home/zhetao/Sources/kremlin/include -I /home/zhetao/Sources/kremlin/kremlib/dist/generic -I /home/zhetao/Sources/hacl-star/specs -I /home/zhetao/Sources/hacl-star/specs/lemmas -I /home/zhetao/Sources/hacl-star/code/hash -I /home/zhetao/Sources/hacl-star/code/hkdf -I /home/zhetao/Sources/hacl-star/code/hmac -I /home/zhetao/Sources/hacl-star/code/curve25519 -I /home/zhetao/Sources/hacl-star/code/ed25519 -I /home/zhetao/Sources/hacl-star/lib -I /home/zhetao/Sources/hacl-star/providers/evercrypt -I /home/zhetao/Sources/kremlin/kremlib -o dice.exe
  F* version: 9c3c5d28
  KreMLin version: fe104c22
 */
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "kremlin/internal/compat.h"

#ifndef __Hacl_Ed25519_H
#define __Hacl_Ed25519_H




extern void
Hacl_Ed25519_sign(
  Lib_IntTypes_sec_int_t____ *signature,
  Lib_IntTypes_sec_int_t____ *secret1,
  uint32_t len,
  Lib_IntTypes_sec_int_t____ *msg
);

extern bool
Hacl_Ed25519_verify(
  Lib_IntTypes_sec_int_t____ *output,
  uint32_t len,
  Lib_IntTypes_sec_int_t____ *msg,
  Lib_IntTypes_sec_int_t____ *signature
);

extern void
Hacl_Ed25519_secret_to_public(
  Lib_IntTypes_sec_int_t____ *output,
  Lib_IntTypes_sec_int_t____ *secret1
);

extern void
Hacl_Ed25519_expand_keys(Lib_IntTypes_sec_int_t____ *ks, Lib_IntTypes_sec_int_t____ *secret1);

extern void
Hacl_Ed25519_sign_expanded(
  Lib_IntTypes_sec_int_t____ *signature,
  Lib_IntTypes_sec_int_t____ *ks,
  uint32_t len,
  Lib_IntTypes_sec_int_t____ *msg
);

#define __Hacl_Ed25519_H_DEFINED
#endif