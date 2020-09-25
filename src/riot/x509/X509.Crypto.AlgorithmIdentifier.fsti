module X509.Crypto.AlgorithmIdentifier

open LowParse.Low.Base

open ASN1.Spec
open ASN1.Low

open X509.Base

open FStar.Integers

(* Payload *)

// type algorithmIdentifier_ECDSA_P256_t = {
//   alg_id_oid_ecdsa: the_asn1_oid OID_EC_ALG_UNRESTRICTED;
//   alg_id_oid_p256 : the_asn1_oid OID_EC_GRP_SECP256R1
// }

type algorithmIdentifier_Ed25519_t = {
  algID_ed25519: the_asn1_oid OID_ED25519
}

let algorithmIdentifier_payload_t
= algorithmIdentifier_Ed25519_t

let parse_algorithmIdentifier_payload_kind
: parser_kind
= parse_asn1_TLV_kind_of_type OID

val parse_algorithmIdentifier_payload
: parser (parse_algorithmIdentifier_payload_kind) (algorithmIdentifier_payload_t)

/// sequence value serializer
val serialize_algorithmIdentifier_payload
: serializer (parse_algorithmIdentifier_payload)

inline_for_extraction
val serialize32_algorithmIdentifier_payload_backwards
: serializer32_backwards (serialize_algorithmIdentifier_payload)

let length_of_algorithmIdentifier_payload ()
: GTot (asn1_value_length_of_type SEQUENCE)
= 5

let len_of_algorithmIdentifier_payload ()
: Tot (len: asn1_value_int32_of_type SEQUENCE
            { v len == length_of_algorithmIdentifier_payload () })
= 5ul

(* Top *)
let algorithmIdentifier_t
= inbound_sequence_value_of (serialize_algorithmIdentifier_payload)

val parse_algorithmIdentifier
: parser (parse_asn1_envelop_tag_with_TLV_kind SEQUENCE) (algorithmIdentifier_t)

val serialize_algorithmIdentifier
: serializer (parse_algorithmIdentifier)

inline_for_extraction
val serialize32_algorithmIdentifier_backwards
: serializer32_backwards (serialize_algorithmIdentifier)

val lemma_serialize_algorithmIdentifier_unfold
  (x: algorithmIdentifier_t)
: Lemma ( predicate_serialize_asn1_sequence_TLV_unfold (serialize_algorithmIdentifier_payload) x )

val lemma_serialize_algorithmIdentifier_size
  (x: algorithmIdentifier_t)
: Lemma ( predicate_serialize_asn1_sequence_TLV_size (serialize_algorithmIdentifier_payload) x )

let length_of_algorithmIdentifier ()
: GTot (asn1_TLV_length_of_type SEQUENCE)
= length_of_TLV SEQUENCE (length_of_algorithmIdentifier_payload ())

let len_of_algorithmIdentifier ()
: Tot (len: asn1_TLV_int32_of_type SEQUENCE
            { v len == length_of_algorithmIdentifier () })
= len_of_TLV SEQUENCE (len_of_algorithmIdentifier_payload ())

val lemma_serialize_algorithmIdentifier_size_exact
  (x: algorithmIdentifier_t)
: Lemma (
  // lemma_serialize_algorithmIdentifier_payload_size x;
  length_of_opaque_serialization (serialize_algorithmIdentifier) x
  == length_of_algorithmIdentifier ()
)

noextract inline_for_extraction
val x509_get_algorithmIdentifier (_: unit)
: Tot (x: algorithmIdentifier_t
          { x.algID_ed25519 == OID_ED25519 })
