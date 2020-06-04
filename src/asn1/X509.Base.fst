module X509.Base

open LowParse.Spec.Base
open LowParse.Spec.Combinators

open ASN1.Base
open ASN1.Spec

open FStar.Integers

module B32 = FStar.Bytes

type cryptoAlg =
| ECDSA_P256

unfold
let pubkey_len
  (pubkey_alg: cryptoAlg)
= match pubkey_alg with
  | ECDSA_P256 -> 32ul

unfold
let pubkey_t
  (pubkey_alg: cryptoAlg)
= match pubkey_alg with
  | ECDSA_P256 -> B32.lbytes32 (pubkey_len pubkey_alg)
