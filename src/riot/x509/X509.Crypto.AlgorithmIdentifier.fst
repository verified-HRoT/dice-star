module X509.Crypto.AlgorithmIdentifier

open LowParse.Low.Base
// open LowParse.Low.Combinators

open ASN1.Spec
open ASN1.Low

open X509.Base

open FStar.Integers

#set-options "--z3rlimit 32"
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

let parse_algorithmIdentifier_payload_kind
: parser_kind
= parse_asn1_TLV_kind_of_type OID

/// sequence value (body) parser
let parse_algorithmIdentifier_payload
: parser (parse_algorithmIdentifier_payload_kind) (algorithmIdentifier_payload_t)
= parse_asn1_oid_TLV_of OID_ED25519
  `parse_synth`
  synth_algorithmIdentifier_payload_t

/// sequence value serializer
let serialize_algorithmIdentifier_payload
: serializer (parse_algorithmIdentifier_payload)
= serialize_synth
  (* p1 *) (parse_asn1_oid_TLV_of OID_ED25519)
  (* f2 *) (synth_algorithmIdentifier_payload_t)
  (* s1 *) (serialize_asn1_oid_TLV_of OID_ED25519)
  (* g1 *) (synth_algorithmIdentifier_payload_t')
  (* prf*) ()

/// lemma: unfold sequence value serializer
let lemma_serialize_algorithmIdentifier_payload_unfold
  (x: algorithmIdentifier_payload_t)
: Lemma (
  serialize (serialize_algorithmIdentifier_payload) x ==
  serialize (serialize_asn1_oid_TLV_of OID_ED25519) OID_ED25519 /\
  length_of_opaque_serialization (serialize_algorithmIdentifier_payload) x ==
  5
)
= serialize_synth_eq
  (* p1 *) (parse_asn1_oid_TLV_of OID_ED25519)
  (* f2 *) (synth_algorithmIdentifier_payload_t)
  (* s1 *) (serialize_asn1_oid_TLV_of OID_ED25519)
  (* g1 *) (synth_algorithmIdentifier_payload_t')
  (* prf*) ()
  (* in *) (x);
  assert_norm (length_of_asn1_primitive_TLV OID_ED25519 == 5)

///
///
/// lemma: reveal sequence serialization size

let length_of_algorithmIdentifier_payload ()
: GTot (asn1_value_length_of_type SEQUENCE)
= 5

let len_of_algorithmIdentifier_payload ()
: Tot (len: asn1_value_int32_of_type SEQUENCE
            { v len == length_of_algorithmIdentifier_payload () })
= 5ul

let lemma_serialize_algorithmIdentifier_payload_size
  (x: algorithmIdentifier_payload_t)
: Lemma (
  length_of_opaque_serialization (serialize_algorithmIdentifier_payload) x
  == length_of_algorithmIdentifier_payload ()
)
= lemma_serialize_algorithmIdentifier_payload_unfold x;
  assert_norm (length_of_asn1_primitive_TLV #OID x.algID_ed25519 == 5)

/// inbound record repr
let algorithmIdentifier_t
= inbound_sequence_value_of (serialize_algorithmIdentifier_payload)

/// TLV
// unfold
let parse_algorithmIdentifier
: parser (parse_asn1_envelop_tag_with_TLV_kind SEQUENCE) (algorithmIdentifier_t)
= parse_asn1_sequence_TLV (serialize_algorithmIdentifier_payload)

let serialize_algorithmIdentifier
: serializer (parse_algorithmIdentifier)
= serialize_asn1_sequence_TLV (serialize_algorithmIdentifier_payload)

let lemma_serialize_algorithmIdentifier_unfold
  (x: algorithmIdentifier_t)
: Lemma ( predicate_serialize_asn1_sequence_TLV_unfold (serialize_algorithmIdentifier_payload) x )
= lemma_serialize_asn1_sequence_TLV_unfold (serialize_algorithmIdentifier_payload) x

let lemma_serialize_algorithmIdentifier_size
  (x: algorithmIdentifier_t)
: Lemma ( predicate_serialize_asn1_sequence_TLV_size (serialize_algorithmIdentifier_payload) x )
= lemma_serialize_asn1_sequence_TLV_size (serialize_algorithmIdentifier_payload) x

let length_of_algorithmIdentifier ()
: GTot (asn1_TLV_length_of_type SEQUENCE)
= length_of_TLV SEQUENCE (length_of_algorithmIdentifier_payload ())

let len_of_algorithmIdentifier ()
: Tot (len: asn1_TLV_int32_of_type SEQUENCE
            { v len == length_of_algorithmIdentifier () })
= len_of_TLV SEQUENCE (len_of_algorithmIdentifier_payload ())

#push-options "--z3rlimit 32 --fuel 0 --ifuel 0"
let lemma_serialize_algorithmIdentifier_size_exact
  // (alg: supported_crypto_alg_t {alg == AlgID_Ed25519})
  (x: algorithmIdentifier_t)
: Lemma (
  lemma_serialize_algorithmIdentifier_payload_size x;
  length_of_opaque_serialization (serialize_algorithmIdentifier) x
  == length_of_algorithmIdentifier ()
)
= lemma_serialize_algorithmIdentifier_payload_size x;
  lemma_serialize_asn1_sequence_TLV_unfold (serialize_algorithmIdentifier_payload) x;
  lemma_serialize_asn1_sequence_TLV_size   (serialize_algorithmIdentifier_payload) x;
  // lemma_serialize_algorithmIdentifier_size alg x;
  assert (length_of_TLV OID (length_of_opaque_serialization (serialize_algorithmIdentifier_payload) x) == 7)
#pop-options

/// Low
///

inline_for_extraction
let serialize32_algorithmIdentifier_payload_backwards
: serializer32_backwards (serialize_algorithmIdentifier_payload)
= serialize32_synth_backwards
  (* ls *) (serialize32_asn1_oid_TLV_of_backwards OID_ED25519)
  (* f2 *) (synth_algorithmIdentifier_payload_t)
  (* g1 *) (synth_algorithmIdentifier_payload_t')
  (* g1'*) (synth_algorithmIdentifier_payload_t')
  (* prf*) ()

inline_for_extraction
let serialize32_algorithmIdentifier_backwards
: serializer32_backwards (serialize_algorithmIdentifier)
= serialize32_asn1_sequence_TLV_backwards
  (* s32 *) (serialize32_algorithmIdentifier_payload_backwards)

(* helpers *)

noextract inline_for_extraction
let x509_get_algorithmIdentifier ()
: Tot (algorithmIdentifier_t)
= let algID: algorithmIdentifier_payload_t = { algID_ed25519 = OID_ED25519 } in
  (* Prf *) lemma_serialize_algorithmIdentifier_payload_size algID;
  (* Prf *) (**) lemma_serialize_asn1_oid_TLV_size algID.algID_ed25519;
  (* return *) algID

