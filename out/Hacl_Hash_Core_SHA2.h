/* 
  This file was generated by KreMLin <https://github.com/FStarLang/kremlin>
  KreMLin invocation: krml -no-prefix Minimal.Main ../src/Minimal.Main.fst -skip-compilation -tmpdir ../out -I /home/zhetao/Sources/hacl-star/specs -I /home/zhetao/Sources/hacl-star/specs/lemmas -I /home/zhetao/Sources/hacl-star/code/hash -I /home/zhetao/Sources/hacl-star/code/hkdf -I /home/zhetao/Sources/hacl-star/code/hmac -I /home/zhetao/Sources/hacl-star/code/curve25519 -I /home/zhetao/Sources/hacl-star/code/ed25519 -I /home/zhetao/Sources/hacl-star/lib -I /home/zhetao/Sources/hacl-star/providers/evercrypt -warn-error +11
  F* version: 953b2211
  KreMLin version: e324b7e6
 */

#include "kremlib.h"
#ifndef __Hacl_Hash_Core_SHA2_H
#define __Hacl_Hash_Core_SHA2_H




extern Lib_IntTypes_sec_int_t____ *Hacl_Hash_Core_SHA2_alloca_224();

extern Lib_IntTypes_sec_int_t____ *Hacl_Hash_Core_SHA2_alloca_256();

extern Lib_IntTypes_sec_int_t____ *Hacl_Hash_Core_SHA2_alloca_384();

extern Lib_IntTypes_sec_int_t____ *Hacl_Hash_Core_SHA2_alloca_512();

extern void Hacl_Hash_Core_SHA2_init_224(Lib_IntTypes_sec_int_t____ *uu____265);

extern void Hacl_Hash_Core_SHA2_init_256(Lib_IntTypes_sec_int_t____ *uu____310);

extern void Hacl_Hash_Core_SHA2_init_384(Lib_IntTypes_sec_int_t____ *uu____355);

extern void Hacl_Hash_Core_SHA2_init_512(Lib_IntTypes_sec_int_t____ *uu____400);

extern void
Hacl_Hash_Core_SHA2_update_224(
  Lib_IntTypes_sec_int_t____ *uu____456,
  Lib_IntTypes_sec_int_t____ *x0
);

extern void
Hacl_Hash_Core_SHA2_update_256(
  Lib_IntTypes_sec_int_t____ *uu____525,
  Lib_IntTypes_sec_int_t____ *x0
);

extern void
Hacl_Hash_Core_SHA2_update_384(
  Lib_IntTypes_sec_int_t____ *uu____594,
  Lib_IntTypes_sec_int_t____ *x0
);

extern void
Hacl_Hash_Core_SHA2_update_512(
  Lib_IntTypes_sec_int_t____ *uu____663,
  Lib_IntTypes_sec_int_t____ *x0
);

extern void Hacl_Hash_Core_SHA2_pad_224(uint64_t uu____728, Lib_IntTypes_sec_int_t____ *x0);

extern void Hacl_Hash_Core_SHA2_pad_256(uint64_t uu____785, Lib_IntTypes_sec_int_t____ *x0);

extern void
Hacl_Hash_Core_SHA2_pad_384(FStar_UInt128_uint128 uu____843, Lib_IntTypes_sec_int_t____ *x0);

extern void
Hacl_Hash_Core_SHA2_pad_512(FStar_UInt128_uint128 uu____903, Lib_IntTypes_sec_int_t____ *x0);

extern void
Hacl_Hash_Core_SHA2_finish_224(
  Lib_IntTypes_sec_int_t____ *uu____964,
  Lib_IntTypes_sec_int_t____ *x0
);

extern void
Hacl_Hash_Core_SHA2_finish_256(
  Lib_IntTypes_sec_int_t____ *uu____1027,
  Lib_IntTypes_sec_int_t____ *x0
);

extern void
Hacl_Hash_Core_SHA2_finish_384(
  Lib_IntTypes_sec_int_t____ *uu____1090,
  Lib_IntTypes_sec_int_t____ *x0
);

extern void
Hacl_Hash_Core_SHA2_finish_512(
  Lib_IntTypes_sec_int_t____ *uu____1153,
  Lib_IntTypes_sec_int_t____ *x0
);

#define __Hacl_Hash_Core_SHA2_H_DEFINED
#endif
