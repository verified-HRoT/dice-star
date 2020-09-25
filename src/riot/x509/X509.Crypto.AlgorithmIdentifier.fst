module X509.Crypto.AlgorithmIdentifier

open LowParse.Low.Base

open ASN1.Spec
open ASN1.Low

open X509.Base

open FStar.Integers

#set-options "--z3rlimit 32"

(* AlgorithmIdentifiers
  ======================
  NOTE: Different algorithms have identifiers in different structure.
*)

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

inline_for_extraction
let serialize32_algorithmIdentifier_payload_backwards
: serializer32_backwards (serialize_algorithmIdentifier_payload)
= serialize32_synth_backwards
  (* ls *) (serialize32_asn1_oid_TLV_of_backwards OID_ED25519)
  (* f2 *) (synth_algorithmIdentifier_payload_t)
  (* g1 *) (synth_algorithmIdentifier_payload_t')
  (* g1'*) (synth_algorithmIdentifier_payload_t')
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

let lemma_serialize_algorithmIdentifier_payload_size
  (x: algorithmIdentifier_payload_t)
: Lemma (
  length_of_opaque_serialization (serialize_algorithmIdentifier_payload) x
  == length_of_algorithmIdentifier_payload ()
)
= lemma_serialize_algorithmIdentifier_payload_unfold x;
  assert_norm (length_of_asn1_primitive_TLV #OID x.algID_ed25519 == 5)

/// TLV
// unfold
let parse_algorithmIdentifier
: parser (parse_asn1_envelop_tag_with_TLV_kind SEQUENCE) (algorithmIdentifier_t)
= parse_asn1_sequence_TLV (serialize_algorithmIdentifier_payload)

let serialize_algorithmIdentifier
: serializer (parse_algorithmIdentifier)
= serialize_asn1_sequence_TLV (serialize_algorithmIdentifier_payload)

inline_for_extraction
let serialize32_algorithmIdentifier_backwards
: serializer32_backwards (serialize_algorithmIdentifier)
= serialize32_asn1_sequence_TLV_backwards
  (* s32 *) (serialize32_algorithmIdentifier_payload_backwards)

let lemma_serialize_algorithmIdentifier_unfold
  (x: algorithmIdentifier_t)
: Lemma ( predicate_serialize_asn1_sequence_TLV_unfold (serialize_algorithmIdentifier_payload) x )
= lemma_serialize_asn1_sequence_TLV_unfold (serialize_algorithmIdentifier_payload) x

let lemma_serialize_algorithmIdentifier_size
  (x: algorithmIdentifier_t)
: Lemma ( predicate_serialize_asn1_sequence_TLV_size (serialize_algorithmIdentifier_payload) x )
= lemma_serialize_asn1_sequence_TLV_size (serialize_algorithmIdentifier_payload) x

let lemma_serialize_algorithmIdentifier_size_exact
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

(* helpers *)

noextract inline_for_extraction
let x509_get_algorithmIdentifier ()
: Tot (algorithmIdentifier_t)
= let algID: algorithmIdentifier_payload_t = { algID_ed25519 = OID_ED25519 } in
  (* Prf *) lemma_serialize_algorithmIdentifier_payload_size algID;
  (* Prf *) (**) lemma_serialize_asn1_oid_TLV_size algID.algID_ed25519;
  (* return *) algID

