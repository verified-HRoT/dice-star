module X509.Crypto.Signature

open LowParse.Low.Base
// open LowParse.Low.Combinators

open ASN1.Spec
open ASN1.Low

open X509.Base

open FStar.Integers
module B32 = FStar.Bytes

open ASN1.Base

let x509_signature_t
  (alg: cryptoAlg {alg == ED25519})
= match alg with
  | ED25519   -> datatype_of_asn1_type BIT_STRING

let parse_x509_signature_kind
  (alg: cryptoAlg {alg == ED25519})
= match alg with
  | ED25519   -> parse_asn1_TLV_kind_of_type BIT_STRING

let parse_x509_signature
  (alg: cryptoAlg {alg == ED25519})
: parser (parse_x509_signature_kind alg) (x509_signature_t alg)
= match alg with
  | ED25519   -> ( parse_asn1_TLV_of_type BIT_STRING )

let serialize_x509_signature
  (alg: cryptoAlg {alg == ED25519})
: serializer (parse_x509_signature alg)
= match alg with
  | ED25519   -> ( serialize_asn1_TLV_of_type BIT_STRING )

let x509_signature_t_inbound
  (alg: cryptoAlg {alg == ED25519})
= match alg with
  | ED25519   -> ( inbound_sequence_value_of (serialize_x509_signature alg) )

let parse_x509_signature_sequence_TLV
  (alg: cryptoAlg {alg == ED25519})
: parser _ (x509_signature_t_inbound alg)
= match alg with
  | ED25519   -> ( parse_asn1_sequence_TLV (serialize_x509_signature alg) )

let serialize_x509_signature_sequence_TLV
  (alg: cryptoAlg {alg == ED25519})
: serializer (parse_x509_signature_sequence_TLV alg)
= match alg with
  | ED25519   -> ( serialize_asn1_sequence_TLV (serialize_x509_signature alg) )

let lemma_serialize_x509_signature_sequence_TLV_unfold
  (alg: cryptoAlg {alg == ED25519})
  (x: x509_signature_t_inbound alg)
: Lemma ( prop_serialize_asn1_sequence_TLV_unfold (serialize_x509_signature alg) x )
= match alg with
  | ED25519   -> ( lemma_serialize_asn1_sequence_TLV_unfold (serialize_x509_signature alg) x )

let lemma_serialize_x509_signature_sequence_TLV_size
  (alg: cryptoAlg {alg == ED25519})
  (x: x509_signature_t_inbound alg)
: Lemma ( prop_serialize_asn1_sequence_TLV_size (serialize_x509_signature alg) x )
= match alg with
  | ED25519   -> ( lemma_serialize_asn1_sequence_TLV_size (serialize_x509_signature alg) x )

(* Low *)
let serialize32_x509_signature_backwards
  (alg: cryptoAlg {alg == ED25519})
: serializer32_backwards (serialize_x509_signature alg)
= match alg with
  | ED25519   -> ( serialize32_asn1_bit_string_TLV_backwards () )

let serialize32_x509_signature_sequence_TLV_backwards
  (alg: cryptoAlg {alg == ED25519})
: serializer32_backwards (serialize_x509_signature_sequence_TLV alg)
= match alg with
  | ED25519   -> ( serialize32_asn1_sequence_TLV_backwards (serialize32_x509_signature_backwards alg) )
