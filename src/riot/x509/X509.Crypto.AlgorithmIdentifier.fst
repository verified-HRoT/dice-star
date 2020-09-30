module X509.Crypto.AlgorithmIdentifier
open ASN1.Spec
open ASN1.Low

open X509.Base

open FStar.Integers

#set-options "--z3rlimit 32"
(* AlgorithmIdentifiers
  ======================
  NOTE: Different algorithms have identifiers in different structure.
*)

/// sequence value (body) parser
let parse_algorithmIdentifier_payload
= parse_asn1_oid_TLV_of OID_ED25519
  `parse_synth`
  synth_algorithmIdentifier_payload_t

/// sequence value serializer
let serialize_algorithmIdentifier_payload
= serialize_synth
  (* p1 *) (parse_asn1_oid_TLV_of OID_ED25519)
  (* f2 *) (synth_algorithmIdentifier_payload_t)
  (* s1 *) (serialize_asn1_oid_TLV_of OID_ED25519)
  (* g1 *) (synth_algorithmIdentifier_payload_t')
  (* prf*) ()

/// lemma: unfold sequence value serializer
let lemma_serialize_algorithmIdentifier_payload_unfold x
= serialize_synth_eq
  (* p1 *) (parse_asn1_oid_TLV_of OID_ED25519)
  (* f2 *) (synth_algorithmIdentifier_payload_t)
  (* s1 *) (serialize_asn1_oid_TLV_of OID_ED25519)
  (* g1 *) (synth_algorithmIdentifier_payload_t')
  (* prf*) ()
  (* in *) (x);
  assert_norm (length_of_asn1_primitive_TLV OID_ED25519 == 5)

let lemma_serialize_algorithmIdentifier_payload_size x
= lemma_serialize_algorithmIdentifier_payload_unfold x;
  assert_norm (length_of_asn1_primitive_TLV #OID x.algID_ed25519 == 5)

/// TLV
// unfold
let parse_algorithmIdentifier
= parse_asn1_sequence_TLV (serialize_algorithmIdentifier_payload)

let serialize_algorithmIdentifier
= serialize_asn1_sequence_TLV (serialize_algorithmIdentifier_payload)

let lemma_serialize_algorithmIdentifier_unfold x
= lemma_serialize_asn1_sequence_TLV_unfold (serialize_algorithmIdentifier_payload) x

let lemma_serialize_algorithmIdentifier_size x
= lemma_serialize_asn1_sequence_TLV_size (serialize_algorithmIdentifier_payload) x

#push-options "--z3rlimit 32 --fuel 0 --ifuel 0"
let lemma_serialize_algorithmIdentifier_size_exact x
= lemma_serialize_algorithmIdentifier_payload_size x;
  lemma_serialize_asn1_sequence_TLV_unfold (serialize_algorithmIdentifier_payload) x;
  lemma_serialize_asn1_sequence_TLV_size   (serialize_algorithmIdentifier_payload) x;
  // lemma_serialize_algorithmIdentifier_size alg x;
  assert (length_of_TLV OID (length_of_opaque_serialization (serialize_algorithmIdentifier_payload) x) == 7)
#pop-options

/// Low
///

let serialize32_algorithmIdentifier_payload_backwards
= serialize32_synth_backwards
  (* ls *) (serialize32_asn1_oid_TLV_of_backwards OID_ED25519)
  (* f2 *) (synth_algorithmIdentifier_payload_t)
  (* g1 *) (synth_algorithmIdentifier_payload_t')
  (* g1'*) (synth_algorithmIdentifier_payload_t')
  (* prf*) ()

let serialize32_algorithmIdentifier_backwards
= serialize32_asn1_sequence_TLV_backwards
  (* s32 *) (serialize32_algorithmIdentifier_payload_backwards)
