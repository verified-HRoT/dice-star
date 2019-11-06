/* 
  This file was generated by KreMLin <https://github.com/FStarLang/kremlin>
  KreMLin invocation: krml -no-prefix DICE.Core DICE.Core.fst -skip-compilation -tmpdir out -I /home/zhetao/Sources/hacl-star/specs -I /home/zhetao/Sources/hacl-star/specs/lemmas -I /home/zhetao/Sources/hacl-star/code/hash -I /home/zhetao/Sources/hacl-star/code/hkdf -I /home/zhetao/Sources/hacl-star/code/hmac -I /home/zhetao/Sources/hacl-star/code/curve25519 -I /home/zhetao/Sources/hacl-star/code/ed25519 -I /home/zhetao/Sources/hacl-star/lib -I /home/zhetao/Sources/hacl-star/providers/evercrypt -warn-error +11
  F* version: 953b2211
  KreMLin version: e324b7e6
 */

#include "kremlib.h"
#ifndef __DICE_Core_H
#define __DICE_Core_H

#include "Lib_IntTypes.h"
#include "Spec_Hash_Definitions.h"
#include "Hacl_Hash_SHA2.h"
#include "kremlinit.h"
#include "C.h"
#include "FStar.h"


extern Lib_IntTypes_sec_int_t____ *get_UDS(Prims_int size1);

extern Lib_IntTypes_sec_int_t____ *get_Measurement(Spec_Hash_Definitions_hash_alg alg);

extern void
diceSHA256(
  Prims_int size1,
  Lib_IntTypes_sec_int_t____ *data,
  Lib_IntTypes_sec_int_t____ *digest
);

extern void
diceSHA256_2(
  Prims_int size1,
  Lib_IntTypes_sec_int_t____ *data1,
  Prims_int size2,
  Lib_IntTypes_sec_int_t____ *data2,
  Lib_IntTypes_sec_int_t____ *digest
);

extern Prims_int _DICE_UDS_LENGTH;

extern uint32_t _DICE_DIGEST_LENGTH;

exit_code main();

#define __DICE_Core_H_DEFINED
#endif
