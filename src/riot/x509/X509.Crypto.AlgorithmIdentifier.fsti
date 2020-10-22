module X509.Crypto.AlgorithmIdentifier

open ASN1.Spec
open ASN1.Low

open X509.Base

open FStar.Integers

(* AlgorithmIdentifiers
  ======================
  NOTE: Different algorithms have identifiers in different structure.
*)

(* ECDSA Prime256 SHA2 *)
type algorithmIdentifier_ECDSA_P256_t = {
  alg_id_oid_ecdsa: the_asn1_oid OID_EC_ALG_UNRESTRICTED;
  alg_id_oid_p256 : the_asn1_oid OID_EC_GRP_SECP256R1
}

type algorithmIdentifier_Ed25519_t = {
  algID_ed25519: the_asn1_oid OID_ED25519
}

let algorithmIdentifier_payload_t
= algorithmIdentifier_Ed25519_t

let algorithmIdentifier_payload_t'
= the_asn1_oid OID_ED25519


/// tuple repr -> record repr
let synth_algorithmIdentifier_payload_t
  (x': algorithmIdentifier_payload_t')
: GTot (algorithmIdentifier_payload_t)
= { algID_ed25519 = x' }

/// record repr -> tuple repr

inline_for_extraction noextract
let synth_algorithmIdentifier_payload_t'
  (x: algorithmIdentifier_payload_t)
: Tot (x': algorithmIdentifier_payload_t' { x == synth_algorithmIdentifier_payload_t x' })
= x.algID_ed25519

inline_for_extraction noextract
let parse_algorithmIdentifier_payload_kind
: parser_kind
= parse_asn1_TLV_kind_of_type OID

/// sequence value (body) parser
noextract
val parse_algorithmIdentifier_payload
: parser (parse_algorithmIdentifier_payload_kind) (algorithmIdentifier_payload_t)

/// sequence value serializer

noextract
val serialize_algorithmIdentifier_payload
: serializer (parse_algorithmIdentifier_payload)

/// lemma: unfold sequence value serializer
val lemma_serialize_algorithmIdentifier_payload_unfold
  (x: algorithmIdentifier_payload_t)
: Lemma (
  serialize (serialize_algorithmIdentifier_payload) x ==
  serialize (serialize_asn1_oid_TLV_of OID_ED25519) OID_ED25519 /\
  length_of_opaque_serialization (serialize_algorithmIdentifier_payload) x ==
  5
)

///
///
/// lemma: reveal sequence serialization size

let len_of_algorithmIdentifier_payload ()
: Tot (asn1_value_int32_of_type SEQUENCE)
= 5ul

val lemma_serialize_algorithmIdentifier_payload_size
  (x: algorithmIdentifier_payload_t)
: Lemma (
  length_of_opaque_serialization (serialize_algorithmIdentifier_payload) x
  == (v (len_of_algorithmIdentifier_payload ()))
)

/// inbound record repr
let algorithmIdentifier_t
= inbound_sequence_value_of (serialize_algorithmIdentifier_payload)

/// TLV
// unfold
noextract
val parse_algorithmIdentifier
: parser (parse_asn1_envelop_tag_with_TLV_kind SEQUENCE) (algorithmIdentifier_t)

noextract
val serialize_algorithmIdentifier
: serializer (parse_algorithmIdentifier)

val lemma_serialize_algorithmIdentifier_unfold
  (x: algorithmIdentifier_t)
: Lemma ( predicate_serialize_asn1_sequence_TLV_unfold (serialize_algorithmIdentifier_payload) x )

val lemma_serialize_algorithmIdentifier_size
  (x: algorithmIdentifier_t)
: Lemma ( predicate_serialize_asn1_sequence_TLV_size (serialize_algorithmIdentifier_payload) x )

noextract unfold
[@@ "opaque_to_smt"]
let len_of_algorithmIdentifier ()
: Tot (asn1_TLV_int32_of_type SEQUENCE)
= len_of_TLV SEQUENCE (len_of_algorithmIdentifier_payload ())

val lemma_serialize_algorithmIdentifier_size_exact
  // (alg: supported_crypto_alg_t {alg == AlgID_Ed25519})
  (x: algorithmIdentifier_t)
: Lemma (
  lemma_serialize_algorithmIdentifier_payload_size x;
  length_of_opaque_serialization (serialize_algorithmIdentifier) x
  == (v (len_of_algorithmIdentifier ()))
)

/// Low
///

//inline_for_extraction
val serialize32_algorithmIdentifier_payload_backwards
: serializer32_backwards (serialize_algorithmIdentifier_payload)

//inline_for_extraction
val serialize32_algorithmIdentifier_backwards
: serializer32_backwards (serialize_algorithmIdentifier)

(* helpers *)

noextract inline_for_extraction
let x509_get_algorithmIdentifier ()
: Tot (algorithmIdentifier_t)
= let algID: algorithmIdentifier_payload_t = { algID_ed25519 = OID_ED25519 } in
  (* Prf *) lemma_serialize_algorithmIdentifier_payload_size algID;
  (* Prf *) (**) lemma_serialize_asn1_oid_TLV_size algID.algID_ed25519;
  (* return *) algID

