/* 
  This file was generated by KreMLin <https://github.com/FStarLang/kremlin>
  KreMLin invocation: C:\cygwin64\home\aseemr\ev1\kremlin\_build\src\Kremlin.native -skip-compilation ./src/DICE.Core.fst -no-prefix DICE.Definitions -no-prefix DICE.Core -no-prefix HWAbstraction -bundle Hacl.Spec.*,Spec.*[rename=Hacl_Spec] -bundle Lib.*[rename=Hacl_Lib] -drop Lib.IntVector.Intrinsics -fparentheses -fno-shadow -fcurly-braces -bundle LowStar.* -bundle Prims,C.Failure,C,C.String,C.Loops,Spec.Loops,C.Endianness,FStar.*[rename=Hacl_Kremlib] -bundle Meta.* -minimal -add-include "kremlin/internal/types.h" -add-include "kremlin/lowstar_endianness.h" -add-include <string.h> -drop WasmSupport -tmpdir ./out -I ./src -add-include "kremlin/internal/compat.h" -I C:/cygwin64/home/aseemr/ev1/kremlin//include -I C:/cygwin64/home/aseemr/ev1/kremlin//kremlib/dist/generic -I C:/cygwin64/home/aseemr/ev1/hacl-star//specs -I C:/cygwin64/home/aseemr/ev1/hacl-star//specs/lemmas -I C:/cygwin64/home/aseemr/ev1/hacl-star//code/hash -I C:/cygwin64/home/aseemr/ev1/hacl-star//code/hkdf -I C:/cygwin64/home/aseemr/ev1/hacl-star//code/hmac -I C:/cygwin64/home/aseemr/ev1/hacl-star//code/curve25519 -I C:/cygwin64/home/aseemr/ev1/hacl-star//code/ed25519 -I C:/cygwin64/home/aseemr/ev1/hacl-star//lib -I C:/cygwin64/home/aseemr/ev1/hacl-star//providers/evercrypt -I C:/cygwin64/home/aseemr/ev1/kremlin//kremlib -I C:/cygwin64/home/aseemr/ev1/hacl-star//obj -o ./out/dice.exe
  F* version: 9fff18ba
  KreMLin version: fe104c22
 */
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "kremlin/internal/compat.h"

#ifndef __Hacl_Hash_Core_SHA1_H
#define __Hacl_Hash_Core_SHA1_H




extern Lib_IntTypes_sec_int_t____ *Hacl_Hash_Core_SHA1_legacy_alloca();

extern void Hacl_Hash_Core_SHA1_legacy_init(Lib_IntTypes_sec_int_t____ *uu____85);

extern void
Hacl_Hash_Core_SHA1_legacy_update(
  Lib_IntTypes_sec_int_t____ *uu____141,
  Lib_IntTypes_sec_int_t____ *x0
);

extern void Hacl_Hash_Core_SHA1_legacy_pad(uint64_t uu____206, Lib_IntTypes_sec_int_t____ *x0);

extern void
Hacl_Hash_Core_SHA1_legacy_finish(
  Lib_IntTypes_sec_int_t____ *uu____265,
  Lib_IntTypes_sec_int_t____ *x0
);

#define __Hacl_Hash_Core_SHA1_H_DEFINED
#endif
