module X509.Crypto.Signature

open LowParse.Low.Base
// open LowParse.Low.Combinators

open ASN1.Spec
open ASN1.Low

open X509.Base

open FStar.Integers
module B32 = FStar.Bytes
(*)
unfold
let crypto_big_integer_as_octet_string_t
  (alg: cryptoAlg)
= match alg with
  | ECDSA_P256 -> (x: datatype_of_asn1_type OCTET_STRING { v (dfst x) == 32 })

let parse_crypto_big_integer_as_octet_string
  (alg: cryptoAlg)
: parser _ (crypto_big_integer_as_octet_string_t alg)
= match alg with
  | ECDSA_P256 -> crypto_big_integer_as_octet_string_t ECDSA_P256
                  `coerce_parser`
                  parse_asn1_octet_string 32

let serialize_crypto_big_integer_as_octet_string
  (alg: cryptoAlg)
: serializer (parse_crypto_big_integer_as_octet_string alg)
= match alg with
  | ECDSA_P256 -> coerce_parser_serializer
                  (* p2 *) (parse_crypto_big_integer_as_octet_string ECDSA_P256)
                  (* s1 *) (serialize_asn1_octet_string 32)
                  (* prf*) ()
open ASN1.Spec.Value.OCTET_STRING
open ASN1.Spec.Base

let lemma_serialize_crypto_big_integer_as_octet_string_unfold
  (alg: cryptoAlg)
= match alg with
  | ECDSA_P256 -> 

noeq
type signatureValue_ECDSA_P256_t = {
  r: B32.lbytes32 32ul;
  s: B32.lbytes32 32ul
}

let signatureValue_t
  (alg: cryptoAlg)
= match alg with
  | ECDSA_P256 -> signatureValue_ECDSA_P256_t

let signatureValue_t'
  (alg: cryptoAlg)
= match alg with
  | ECDSA_P256 -> (B32.lbytes32 32ul `tuple2` B32.lbytes32 32ul)

let synth_signatureValue_t
  (alg: cryptoAlg)
  (x': signatureValue_t' alg)
: GTot (signatureValue_t alg)
= match alg with
  | ECDSA_P256 -> let r, s = x' <: signatureValue_t' ECDSA_P256 in
                  {r = r; s = s}

let synth_signatureValue_t'
  (alg: cryptoAlg)
  (x: signatureValue_t alg)
: Tot (x': signatureValue_t' alg { x == synth_signatureValue_t alg x' })
= match alg with
  | ECDSA_P256 -> let x = x <: signatureValue_t ECDSA_P256 in
                  (x.r, x.s)
