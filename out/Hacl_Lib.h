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

#ifndef __Hacl_Lib_H
#define __Hacl_Lib_H




#define Lib_IntTypes_U1 0
#define Lib_IntTypes_U8 1
#define Lib_IntTypes_U16 2
#define Lib_IntTypes_U32 3
#define Lib_IntTypes_U64 4
#define Lib_IntTypes_U128 5
#define Lib_IntTypes_S8 6
#define Lib_IntTypes_S16 7
#define Lib_IntTypes_S32 8
#define Lib_IntTypes_S64 9
#define Lib_IntTypes_S128 10

typedef uint8_t Lib_IntTypes_inttype;

#define Lib_IntTypes_SEC 0
#define Lib_IntTypes_PUB 1

typedef uint8_t Lib_IntTypes_secrecy_level;

extern void
*Lib_IntTypes_mk_int(Lib_IntTypes_inttype t, Lib_IntTypes_secrecy_level l, Prims_int n1);

extern bool Lib_IntTypes_lt(Lib_IntTypes_inttype t, void *uu____17924, void *uu____17925);

#define __Hacl_Lib_H_DEFINED
#endif