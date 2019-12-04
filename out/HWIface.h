/* 
  This file was generated by KreMLin <https://github.com/FStarLang/kremlin>
  KreMLin invocation: krml -no-prefix Minimal.DICE ./src/Minimal.DICE.fst -skip-compilation -tmpdir ./out -I ./src -I /home/zhetao/Sources/hacl-star/specs -I /home/zhetao/Sources/hacl-star/specs/lemmas -I /home/zhetao/Sources/hacl-star/code/hash -I /home/zhetao/Sources/hacl-star/code/hkdf -I /home/zhetao/Sources/hacl-star/code/hmac -I /home/zhetao/Sources/hacl-star/code/curve25519 -I /home/zhetao/Sources/hacl-star/code/ed25519 -I /home/zhetao/Sources/hacl-star/lib -I /home/zhetao/Sources/hacl-star/providers/evercrypt -warn-error +11
  F* version: 953b2211
  KreMLin version: e324b7e6
 */

#include "kremlib.h"
#ifndef __HWIface_H
#define __HWIface_H

#include "Spec_Hash_Definitions.h"


typedef Spec_Hash_Definitions_hash_alg HWIface_dice_alg;

extern Spec_Hash_Definitions_hash_alg HWIface_alg;

extern uint32_t HWIface_digest_length;

extern uint32_t HWIface_uds_length;

extern uint32_t HWIface_cdi_length;

typedef uint32_t HWIface_riot_size_t;

extern void **HWIface_local_state;

extern Lib_IntTypes_sec_int_t____ *HWIface_get_uds(HWIface_state st);

extern Lib_IntTypes_sec_int_t____ *HWIface_get_cdi(HWIface_state st);

extern HWIface_state HWIface_initialize(Lib_IntTypes_sec_int_t____ *riot_binary);

extern void HWIface_unset_uds(HWIface_state st);

extern void HWIface_disable_uds(HWIface_state st);

#define __HWIface_H_DEFINED
#endif
