module X509.Crypto.Signature

open ASN1.Spec
open ASN1.Low

open X509.Base

open FStar.Integers

open ASN1.Base

let x509_signature_t_aux
  // (alg: supported_crypto_alg_t {alg == AlgID_Ed25519})
=
  // match alg with
  // | AlgID_Ed25519   ->
  datatype_of_asn1_type BIT_STRING

let filter_x509_signature
  // (alg: supported_crypto_alg_t {alg == AlgID_Ed25519})
  (x: x509_signature_t_aux)
: GTot (bool)
=
  // match alg with
  // | AlgID_Ed25519   ->
  ( let x = x <: datatype_of_asn1_type BIT_STRING in
                   x.bs_len = 65ul &&
                   x.bs_unused_bits = 0ul )

let x509_signature_t
  // (alg: supported_crypto_alg_t {alg == AlgID_Ed25519})
=
  // match alg with
  // | AlgID_Ed25519   ->
  ( bs: datatype_of_asn1_type BIT_STRING
                       { v bs.bs_len == 65 /\
                         v bs.bs_unused_bits == 0 })

let parse_x509_signature_kind
  // (alg: supported_crypto_alg_t {alg == AlgID_Ed25519})
=
  // match alg with
  // | AlgID_Ed25519   ->
  parse_asn1_TLV_kind_of_type BIT_STRING

noextract
val parse_x509_signature
  // (alg: supported_crypto_alg_t {alg == AlgID_Ed25519})
: parser (parse_x509_signature_kind) (x509_signature_t)

noextract
val serialize_x509_signature
  // (alg: supported_crypto_alg_t {alg == AlgID_Ed25519})
: serializer (parse_x509_signature)

val lemma_serialize_x509_signature_unfold
  // (alg: supported_crypto_alg_t {alg == AlgID_Ed25519})
  (x: x509_signature_t)
: Lemma (
  // match alg with
  // | AlgID_Ed25519   ->
                 ( serialize_x509_signature `serialize` x ==
                   serialize_asn1_TLV_of_type BIT_STRING x )
)

val lemma_serialize_x509_signature_size
  // (alg: supported_crypto_alg_t {alg == AlgID_Ed25519})
  (x: x509_signature_t)
: Lemma (
  // match alg with
  // | AlgID_Ed25519   ->
  ( length_of_opaque_serialization (serialize_x509_signature) x ==
                   length_of_asn1_primitive_TLV #BIT_STRING x /\
                   length_of_opaque_serialization (serialize_x509_signature) x == 67 )
)

///
///
(*)
let x509_signature_t_inbound
  // (alg: supported_crypto_alg_t {alg == AlgID_Ed25519})
=
  // match alg with
  // | AlgID_Ed25519   ->
  ( inbound_sequence_value_of (serialize_x509_signature) )

let parse_x509_signature_sequence_TLV
  // (alg: supported_crypto_alg_t {alg == AlgID_Ed25519})
: parser _ (x509_signature_t_inbound)
=
  // match alg with
  // | AlgID_Ed25519   ->
  ( parse_asn1_sequence_TLV (serialize_x509_signature) )

let serialize_x509_signature_sequence_TLV
  // (alg: supported_crypto_alg_t {alg == AlgID_Ed25519})
: serializer (parse_x509_signature_sequence_TLV)
=
  // match alg with
  // | AlgID_Ed25519   ->
  ( serialize_asn1_sequence_TLV (serialize_x509_signature) )

let lemma_serialize_x509_signature_sequence_TLV_unfold
  // (alg: supported_crypto_alg_t {alg == AlgID_Ed25519})
  (x: x509_signature_t_inbound)
: Lemma ( predicate_serialize_asn1_sequence_TLV_unfold (serialize_x509_signature) x )
=
  // match alg with
  // | AlgID_Ed25519   ->
  ( lemma_serialize_asn1_sequence_TLV_unfold (serialize_x509_signature) x )

let lemma_serialize_x509_signature_sequence_TLV_size
  // (alg: supported_crypto_alg_t {alg == AlgID_Ed25519})
  (x: x509_signature_t_inbound)
: Lemma ( predicate_serialize_asn1_sequence_TLV_size (serialize_x509_signature) x )
=
  // match alg with
  // | AlgID_Ed25519   ->
  ( lemma_serialize_asn1_sequence_TLV_size (serialize_x509_signature) x )

#push-options "--z3rlimit 32 --fuel 0 --ifuel 0"
let lemma_serialize_x509_signature_sequence_TLV_size_exact
  // (alg: supported_crypto_alg_t {alg == AlgID_Ed25519})
  (x: x509_signature_t_inbound)
: Lemma (
  // match alg with
  // | AlgID_Ed25519    ->
  ( length_of_opaque_serialization (serialize_x509_signature_sequence_TLV) x == 69 )
)
=
  // match alg with
  // | AlgID_Ed25519    ->
  ( lemma_serialize_x509_signature_sequence_TLV_size x;
                    lemma_serialize_x509_signature_size x )
#pop-options
*)

(* Low *)
inline_for_extraction
val serialize32_x509_signature_backwards
  // (alg: supported_crypto_alg_t {alg == AlgID_Ed25519})
: serializer32_backwards (serialize_x509_signature)

(*)
inline_for_extraction
let serialize32_x509_signature_sequence_TLV_backwards
  // (alg: supported_crypto_alg_t {alg == AlgID_Ed25519})
: serializer32_backwards (serialize_x509_signature_sequence_TLV)
=
  // match alg with
  // | AlgID_Ed25519   ->
  ( serialize32_asn1_sequence_TLV_backwards (serialize32_x509_signature_backwards) )
*)

(* Helpers *)

module B32 = FStar.Bytes
let x509_signature_raw_t
  // (alg: supported_crypto_alg_t {alg == AlgID_Ed25519})
=
  // match alg with
  // | AlgID_Ed25519   ->
  ( B32.lbytes32 64ul )

inline_for_extraction noextract
let x509_get_signature
  // (alg: supported_crypto_alg_t {alg == AlgID_Ed25519})
  (sig32: x509_signature_raw_t)
: Tot (x509_signature_t)
=
  // match alg with
  // | AlgID_Ed25519   ->
  ( let sig_bs: x509_signature_t = Mkbit_string_t 65ul 0ul sig32 in
                   (* Prf *) lemma_serialize_x509_signature_size sig_bs;
                   (* return *) sig_bs )
