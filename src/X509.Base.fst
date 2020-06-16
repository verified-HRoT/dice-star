module X509.Base

open LowParse.Spec.Base
open LowParse.Spec.Combinators

open ASN1.Base
open ASN1.Spec

open FStar.Integers

module B32 = FStar.Bytes

(* Disabling them for now *)
// type supported_crypto_alg_t =
// | AlgID_ECDSA_P256
// | AlgID_Ed25519

unfold
let pubkey_len
  // (pubkey_alg: supported_crypto_alg_t)
=
  // match pubkey_alg with
  // | AlgID_ECDSA_P256 -> 32ul
  // | AlgID_Ed25519    ->
  32ul

unfold
let pubkey_t
  // (pubkey_alg: supported_crypto_alg_t)
=
  // match pubkey_alg with
  // | AlgID_ECDSA_P256 -> datatype_of_asn1_type BIT_STRING
  // | AlgID_Ed25519    ->
  bs: datatype_of_asn1_type BIT_STRING
                     { bs.bs_len == 33ul /\
                       bs.bs_unused_bits == 0ul}
