module X509.Base

open LowParse.Spec.Base
open LowParse.Spec.Combinators

open ASN1.Base
open ASN1.Spec

open FStar.Integers

module B32 = FStar.Bytes

type cryptoAlg =
| ECDSA_P256
| ED25519

unfold
let pubkey_len
  (pubkey_alg: cryptoAlg)
= match pubkey_alg with
  | ECDSA_P256 -> 32ul
  | ED25519    -> 32ul

unfold
let pubkey_t
  (pubkey_alg: cryptoAlg)
= match pubkey_alg with
  | ECDSA_P256 -> datatype_of_asn1_type BIT_STRING
  | ED25519    -> bs: datatype_of_asn1_type BIT_STRING
                     { bs.bs_len == 33ul /\
                       bs.bs_unused_bits == 0ul}
