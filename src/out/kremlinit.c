/* 
  This file was generated by KreMLin <https://github.com/FStarLang/kremlin>
  KreMLin invocation: krml -no-prefix Minimal.Main Minimal.Main.fst -skip-compilation -tmpdir out -I /home/zhetao/Sources/hacl-star/specs -I /home/zhetao/Sources/hacl-star/specs/lemmas -I /home/zhetao/Sources/hacl-star/code/hash -I /home/zhetao/Sources/hacl-star/code/hkdf -I /home/zhetao/Sources/hacl-star/code/hmac -I /home/zhetao/Sources/hacl-star/code/curve25519 -I /home/zhetao/Sources/hacl-star/code/ed25519 -I /home/zhetao/Sources/hacl-star/lib -I /home/zhetao/Sources/hacl-star/providers/evercrypt -warn-error +11
  F* version: 953b2211
  KreMLin version: e324b7e6
 */

#include "kremlinit.h"


#if defined(__GNUC__) && !(defined(_WIN32) || defined(_WIN64))
__attribute__ ((visibility ("hidden")))
#endif


void kremlinit_globals()
{
  Lib_IntTypes_max_size_t =
    Prims_op_Subtraction(Prims_pow2((krml_checked_int_t)32),
      (krml_checked_int_t)1);
  uint32_t sw;
  switch (Minimal_RIoT__RIOT_ALG)
  {
    case Spec_Hash_Definitions_MD5:
      {
        sw = (uint32_t)16U;
        break;
      }
    case Spec_Hash_Definitions_SHA1:
      {
        sw = (uint32_t)20U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_224:
      {
        sw = (uint32_t)28U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        sw = (uint32_t)32U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        sw = (uint32_t)48U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        sw = (uint32_t)64U;
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  Minimal_RIoT__RIOT_DIGEST_LENGTH = sw;
  uint32_t sw0;
  switch (Minimal_DICE__DICE_ALG)
  {
    case Spec_Hash_Definitions_MD5:
      {
        sw0 = (uint32_t)16U;
        break;
      }
    case Spec_Hash_Definitions_SHA1:
      {
        sw0 = (uint32_t)20U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_224:
      {
        sw0 = (uint32_t)28U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        sw0 = (uint32_t)32U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        sw0 = (uint32_t)48U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        sw0 = (uint32_t)64U;
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  Minimal_DICE__DICE_DIGEST_LENGTH = sw0;
}

