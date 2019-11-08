/* 
  This file was generated by KreMLin <https://github.com/FStarLang/kremlin>
  KreMLin invocation: krml -no-prefix Minimal.Main Minimal.Main.fst -skip-compilation -tmpdir out -I /home/zhetao/Sources/hacl-star/specs -I /home/zhetao/Sources/hacl-star/specs/lemmas -I /home/zhetao/Sources/hacl-star/code/hash -I /home/zhetao/Sources/hacl-star/code/hkdf -I /home/zhetao/Sources/hacl-star/code/hmac -I /home/zhetao/Sources/hacl-star/code/curve25519 -I /home/zhetao/Sources/hacl-star/code/ed25519 -I /home/zhetao/Sources/hacl-star/lib -I /home/zhetao/Sources/hacl-star/providers/evercrypt -warn-error +11
  F* version: 953b2211
  KreMLin version: e324b7e6
 */

#include "Lib_ByteSequence.h"

typedef Prims_list__uint8_t *FStar_Seq_Base_seq__uint8_t;

typedef Prims_list__any *FStar_Seq_Base_seq__any;

Prims_int Lib_ByteSequence_nat_from_bytes_be(Lib_IntTypes_secrecy_level l, Prims_list__any *b)
{
  return Lib_ByteSequence_nat_from_intseq_be(Lib_IntTypes_U8, l, b);
}

Prims_int Lib_ByteSequence_nat_from_bytes_le(Lib_IntTypes_secrecy_level l, Prims_list__any *b)
{
  return Lib_ByteSequence_nat_from_intseq_le(Lib_IntTypes_U8, l, b);
}

