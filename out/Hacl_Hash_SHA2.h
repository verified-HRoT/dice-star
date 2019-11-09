/* 
  This file was generated by KreMLin <https://github.com/FStarLang/kremlin>
  KreMLin invocation: krml -no-prefix Minimal.Main ../src/Minimal.Main.fst -skip-compilation -tmpdir ../out -I /home/zhetao/Sources/hacl-star/specs -I /home/zhetao/Sources/hacl-star/specs/lemmas -I /home/zhetao/Sources/hacl-star/code/hash -I /home/zhetao/Sources/hacl-star/code/hkdf -I /home/zhetao/Sources/hacl-star/code/hmac -I /home/zhetao/Sources/hacl-star/code/curve25519 -I /home/zhetao/Sources/hacl-star/code/ed25519 -I /home/zhetao/Sources/hacl-star/lib -I /home/zhetao/Sources/hacl-star/providers/evercrypt -warn-error +11
  F* version: 953b2211
  KreMLin version: e324b7e6
 */

#include "kremlib.h"
#ifndef __Hacl_Hash_SHA2_H
#define __Hacl_Hash_SHA2_H




extern void
Hacl_Hash_SHA2_update_multi_224(
  Lib_IntTypes_sec_int_t____ *uu____342,
  Lib_IntTypes_sec_int_t____ *x0,
  uint32_t x1
);

extern void
Hacl_Hash_SHA2_update_multi_256(
  Lib_IntTypes_sec_int_t____ *uu____423,
  Lib_IntTypes_sec_int_t____ *x0,
  uint32_t x1
);

extern void
Hacl_Hash_SHA2_update_multi_384(
  Lib_IntTypes_sec_int_t____ *uu____504,
  Lib_IntTypes_sec_int_t____ *x0,
  uint32_t x1
);

extern void
Hacl_Hash_SHA2_update_multi_512(
  Lib_IntTypes_sec_int_t____ *uu____585,
  Lib_IntTypes_sec_int_t____ *x0,
  uint32_t x1
);

extern void
Hacl_Hash_SHA2_update_last_224(
  Lib_IntTypes_sec_int_t____ *uu____673,
  uint64_t x0,
  Lib_IntTypes_sec_int_t____ *x1,
  uint32_t x2
);

extern void
Hacl_Hash_SHA2_update_last_256(
  Lib_IntTypes_sec_int_t____ *uu____766,
  uint64_t x0,
  Lib_IntTypes_sec_int_t____ *x1,
  uint32_t x2
);

extern void
Hacl_Hash_SHA2_update_last_384(
  Lib_IntTypes_sec_int_t____ *uu____860,
  FStar_UInt128_uint128 x0,
  Lib_IntTypes_sec_int_t____ *x1,
  uint32_t x2
);

extern void
Hacl_Hash_SHA2_update_last_512(
  Lib_IntTypes_sec_int_t____ *uu____956,
  FStar_UInt128_uint128 x0,
  Lib_IntTypes_sec_int_t____ *x1,
  uint32_t x2
);

extern void
Hacl_Hash_SHA2_hash_224(
  Lib_IntTypes_sec_int_t____ *uu____1042,
  uint32_t x0,
  Lib_IntTypes_sec_int_t____ *x1
);

extern void
Hacl_Hash_SHA2_hash_256(
  Lib_IntTypes_sec_int_t____ *uu____1117,
  uint32_t x0,
  Lib_IntTypes_sec_int_t____ *x1
);

extern void
Hacl_Hash_SHA2_hash_384(
  Lib_IntTypes_sec_int_t____ *uu____1192,
  uint32_t x0,
  Lib_IntTypes_sec_int_t____ *x1
);

extern void
Hacl_Hash_SHA2_hash_512(
  Lib_IntTypes_sec_int_t____ *uu____1267,
  uint32_t x0,
  Lib_IntTypes_sec_int_t____ *x1
);

extern void
Hacl_Hash_SHA2_hash_512_lib(
  uint32_t input_len,
  Lib_IntTypes_sec_int_t____ *input,
  Lib_IntTypes_sec_int_t____ *dst
);

#define __Hacl_Hash_SHA2_H_DEFINED
#endif
