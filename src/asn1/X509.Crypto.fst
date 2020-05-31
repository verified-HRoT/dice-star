module X509.Crypto

open LowParse.Low.Base
// open LowParse.Low.Combinators

open ASN1.Spec
open ASN1.Low

open X509.Base

open FStar.Integers

(* FIXME: ZT: large structs have bad performance. *)

(* AlgorithmIdentifiers
  ======================
  NOTE: Different algorithms have identifiers in different structure.
*)

(* ECDSA Prime256 SHA2 *)
noeq
type algorithmIdentifier_ECDSA_P256_t = {
  alg_id_oid_ecdsa: oid: datatype_of_asn1_type OID {oid == OID_EC_ALG_UNRESTRICTED};
  alg_id_oid_p256 : oid: datatype_of_asn1_type OID {oid == OID_EC_GRP_SECP256R1}
}

/// tuple repr
let filter_algorithmIdentifier_ECDSA_P256_t'
  (x': tuple2 (datatype_of_asn1_type OID) (datatype_of_asn1_type OID))
: GTot bool
= fst x' = OID_EC_ALG_UNRESTRICTED &&
  snd x' = OID_EC_GRP_SECP256R1

let algorithmIdentifier_ECDSA_P256_t'
= parse_filter_refine filter_algorithmIdentifier_ECDSA_P256_t'

/// tuple repr -> record repr
let synth_algorithmIdentifier_ECDSA_P256_t
  (x': algorithmIdentifier_ECDSA_P256_t')
: GTot (algorithmIdentifier_ECDSA_P256_t)
= { alg_id_oid_ecdsa = fst x';
    alg_id_oid_p256  = snd x' }

/// record repr -> tuple repr
let synth_algorithmIdentifier_ECDSA_P256_t'
  (x: algorithmIdentifier_ECDSA_P256_t)
: Tot (x': algorithmIdentifier_ECDSA_P256_t' { x == synth_algorithmIdentifier_ECDSA_P256_t x' })
= (x.alg_id_oid_ecdsa, x.alg_id_oid_p256)

/// sequence value (body) parser
let parse_algorithmIdentifier_sequence_ECDSA_P256
: parser _ algorithmIdentifier_ECDSA_P256_t
= parse_asn1_TLV_of_type OID
  `nondep_then`
  parse_asn1_TLV_of_type OID
  `parse_filter`
  filter_algorithmIdentifier_ECDSA_P256_t'
  `parse_synth`
  synth_algorithmIdentifier_ECDSA_P256_t

/// sequence value serializer
let serialize_algorithmIdentifier_sequence_ECDSA_P256
: serializer parse_algorithmIdentifier_sequence_ECDSA_P256
= serialize_synth
  (* p1 *) (parse_asn1_TLV_of_type OID
            `nondep_then`
            parse_asn1_TLV_of_type OID
            `parse_filter`
            filter_algorithmIdentifier_ECDSA_P256_t')
  (* f2 *) (synth_algorithmIdentifier_ECDSA_P256_t)
  (* s1 *) (serialize_asn1_TLV_of_type OID
            `serialize_nondep_then`
            serialize_asn1_TLV_of_type OID
            `serialize_filter`
            filter_algorithmIdentifier_ECDSA_P256_t')
  (* g1 *) (synth_algorithmIdentifier_ECDSA_P256_t')
  (* prf*) ()

/// lemma: unfold sequence value serializer
let lemma_serialize_algorithmIdentifier_sequence_ECDSA_P256_unfold
  (x: algorithmIdentifier_ECDSA_P256_t)
: Lemma (
  serialize serialize_algorithmIdentifier_sequence_ECDSA_P256 x ==
  serialize (serialize_asn1_TLV_of_type OID) x.alg_id_oid_ecdsa
  `Seq.append`
  serialize (serialize_asn1_TLV_of_type OID) x.alg_id_oid_p256
)
= serialize_nondep_then_eq
  (* s1 *) (serialize_asn1_TLV_of_type OID)
  (* s2 *) (serialize_asn1_TLV_of_type OID)
  (* in *) (synth_algorithmIdentifier_ECDSA_P256_t' x);
  serialize_synth_eq
  (* p1 *) (parse_asn1_TLV_of_type OID
            `nondep_then`
            parse_asn1_TLV_of_type OID
            `parse_filter`
            filter_algorithmIdentifier_ECDSA_P256_t')
  (* f2 *) (synth_algorithmIdentifier_ECDSA_P256_t)
  (* s1 *) (serialize_asn1_TLV_of_type OID
            `serialize_nondep_then`
            serialize_asn1_TLV_of_type OID
            `serialize_filter`
            filter_algorithmIdentifier_ECDSA_P256_t')
  (* g1 *) (synth_algorithmIdentifier_ECDSA_P256_t')
  (* prf*) ()
  (* in *) x

/// lemma: reveal sequence serialization size
let lemma_serialize_algorithmIdentifier_sequence_ECDSA_P256_size
  (x: algorithmIdentifier_ECDSA_P256_t)
: Lemma (
  Seq.length (serialize serialize_algorithmIdentifier_sequence_ECDSA_P256 x) ==
  length_of_asn1_primitive_TLV x.alg_id_oid_ecdsa +
  length_of_asn1_primitive_TLV x.alg_id_oid_p256
)
= lemma_serialize_algorithmIdentifier_sequence_ECDSA_P256_unfold x

/// inbound record repr
let algorithmIdentifier_ECDSA_P256_t_inbound
= inbound_sequence_value_of serialize_algorithmIdentifier_sequence_ECDSA_P256

/// TLV
///
let parse_algorithmIdentifier_sequence_TLV_ECDSA_P256
: parser _ algorithmIdentifier_ECDSA_P256_t_inbound
= parse_asn1_sequence_TLV serialize_algorithmIdentifier_sequence_ECDSA_P256

let serialize_algorithmIdentifier_sequence_TLV_ECDSA_P256
: serializer parse_algorithmIdentifier_sequence_TLV_ECDSA_P256
= serialize_asn1_sequence_TLV serialize_algorithmIdentifier_sequence_ECDSA_P256

let lemma_serialize_algorithmIdentifier_sequence_TLV_ECDSA_P256_unfold
= lemma_serialize_asn1_sequence_TLV_unfold serialize_algorithmIdentifier_sequence_ECDSA_P256

let lemma_serialize_algorithmIdentifier_sequence_TLV_ECDSA_P256_size
= lemma_serialize_asn1_sequence_TLV_size serialize_algorithmIdentifier_sequence_ECDSA_P256

/// Low
///

inline_for_extraction
let serialize32_algorithmIdentifier_sequence_ECDSA_P256_backwards
: serializer32_backwards serialize_algorithmIdentifier_sequence_ECDSA_P256
= serialize32_synth_backwards
  (* ls *) (serialize32_asn1_TLV_backwards_of_type OID
            `serialize32_nondep_then_backwards`
            serialize32_asn1_TLV_backwards_of_type OID
            `serialize32_filter_backwards`
            filter_algorithmIdentifier_ECDSA_P256_t')
  (* f2 *) (synth_algorithmIdentifier_ECDSA_P256_t)
  (* g1 *) (synth_algorithmIdentifier_ECDSA_P256_t')
  (* g1'*) (synth_algorithmIdentifier_ECDSA_P256_t')
  (* prf*) ()

let serialize32_algorithmIdentifier_sequence_TLV_ECDSA_P256_backwards
: serializer32_backwards serialize_algorithmIdentifier_sequence_TLV_ECDSA_P256
= serialize32_asn1_sequence_TLV_backwards
  (* ls *) (serialize32_algorithmIdentifier_sequence_ECDSA_P256_backwards)


(* SubjectPublicKeyInfo
  ======================
*)
/// Record repr
noeq
type subjectPublicKeyInfo_ECDSA_P256_t = {
  subjectPubKey_alg : algorithmIdentifier_ECDSA_P256_t_inbound;
  subjectPubKey     : datatype_of_asn1_type BIT_STRING
}

/// tuple repr
let subjectPublicKeyInfo_ECDSA_P256_t'
= tuple2
  (algorithmIdentifier_ECDSA_P256_t_inbound)
  (datatype_of_asn1_type BIT_STRING)

let synth_subjectPublicKeyInfo_ECDSA_P256_t
  (x': subjectPublicKeyInfo_ECDSA_P256_t')
: GTot (subjectPublicKeyInfo_ECDSA_P256_t)
= { subjectPubKey_alg = fst x';
    subjectPubKey     = snd x' }

let synth_subjectPublicKeyInfo_ECDSA_P256_t'
  (x: subjectPublicKeyInfo_ECDSA_P256_t)
: Tot (x': subjectPublicKeyInfo_ECDSA_P256_t'{ x == synth_subjectPublicKeyInfo_ECDSA_P256_t x' })
= (x.subjectPubKey_alg , x.subjectPubKey)

let parse_subjectPublicKeyInfo_sequence_ECDSA_P256
: parser _ (subjectPublicKeyInfo_ECDSA_P256_t)
= parse_algorithmIdentifier_sequence_TLV_ECDSA_P256
  `nondep_then`
  parse_asn1_TLV_of_type BIT_STRING
  `parse_synth`
  synth_subjectPublicKeyInfo_ECDSA_P256_t

let serialize_subjectPublicKeyInfo_sequence_ECDSA_P256
: serializer (parse_subjectPublicKeyInfo_sequence_ECDSA_P256)
= serialize_synth
  (* p1 *) (parse_algorithmIdentifier_sequence_TLV_ECDSA_P256
            `nondep_then`
            parse_asn1_TLV_of_type BIT_STRING)
  (* f2 *) (synth_subjectPublicKeyInfo_ECDSA_P256_t)
  (* s1 *) (serialize_algorithmIdentifier_sequence_TLV_ECDSA_P256
            `serialize_nondep_then`
            serialize_asn1_TLV_of_type BIT_STRING)
  (* g1 *) (synth_subjectPublicKeyInfo_ECDSA_P256_t')
  (* prf*) ()

let lemma_serialize_subjectPublicKeyInfo_sequence_ECDSA_P256_unfold
  (x: subjectPublicKeyInfo_ECDSA_P256_t)
: Lemma (
  serialize (serialize_subjectPublicKeyInfo_sequence_ECDSA_P256) x ==
  serialize (serialize_algorithmIdentifier_sequence_TLV_ECDSA_P256) x.subjectPubKey_alg
  `Seq.append`
  serialize (serialize_asn1_TLV_of_type BIT_STRING) x.subjectPubKey
)
= serialize_nondep_then_eq
  (* s1 *) (serialize_algorithmIdentifier_sequence_TLV_ECDSA_P256)
  (* s2 *) (serialize_asn1_TLV_of_type BIT_STRING)
  (* in *) (synth_subjectPublicKeyInfo_ECDSA_P256_t' x);
  serialize_synth_eq
  (* p1 *) (parse_algorithmIdentifier_sequence_TLV_ECDSA_P256
            `nondep_then`
            parse_asn1_TLV_of_type BIT_STRING)
  (* f2 *) (synth_subjectPublicKeyInfo_ECDSA_P256_t)
  (* s1 *) (serialize_algorithmIdentifier_sequence_TLV_ECDSA_P256
            `serialize_nondep_then`
            serialize_asn1_TLV_of_type BIT_STRING)
  (* g1 *) (synth_subjectPublicKeyInfo_ECDSA_P256_t')
  (* prf*) ()
  (* in *) x

let lemma_serialize_subjectPublicKeyInfo_sequence_ECDSA_P256_size
  (x: subjectPublicKeyInfo_ECDSA_P256_t)
: Lemma (
  Seq.length (serialize (serialize_subjectPublicKeyInfo_sequence_ECDSA_P256) x) ==
  Seq.length (serialize (serialize_algorithmIdentifier_sequence_TLV_ECDSA_P256) x.subjectPubKey_alg) +
  Seq.length (serialize (serialize_asn1_TLV_of_type BIT_STRING) x.subjectPubKey)
)
= lemma_serialize_subjectPublicKeyInfo_sequence_ECDSA_P256_unfold x

(* NOTE: Define the `inbound` version of value type after we defined then serializer. *)
let subjectPublicKeyInfo_ECDSA_P256_t_inbound
= inbound_sequence_value_of (serialize_subjectPublicKeyInfo_sequence_ECDSA_P256)


/// TLV
///
let parse_subjectPublicKeyInfo_sequence_TLV_ECDSA_P256
: parser _ (subjectPublicKeyInfo_ECDSA_P256_t_inbound)
= parse_asn1_sequence_TLV (serialize_subjectPublicKeyInfo_sequence_ECDSA_P256)

let serialize_subjectPublicKeyInfo_sequence_TLV_ECDSA_P256
: serializer (parse_subjectPublicKeyInfo_sequence_TLV_ECDSA_P256)
= serialize_asn1_sequence_TLV (serialize_subjectPublicKeyInfo_sequence_ECDSA_P256)

let lemma_serialize_subjectPublicKeyInfo_sequence_TLV_ECDSA_P256_unfold
= lemma_serialize_asn1_sequence_TLV_unfold (serialize_subjectPublicKeyInfo_sequence_ECDSA_P256)

let lemma_serialize_subjectPublicKeyInfo_sequence_TLV_ECDSA_P256_size
= lemma_serialize_asn1_sequence_TLV_size (serialize_subjectPublicKeyInfo_sequence_ECDSA_P256)

/// Low
///

inline_for_extraction
let serialize32_subjectPublicKeyInfo_sequence_ECDSA_P256_backwards
: serializer32_backwards (serialize_subjectPublicKeyInfo_sequence_ECDSA_P256)
= serialize32_synth_backwards
  (* ls *) (serialize32_algorithmIdentifier_sequence_TLV_ECDSA_P256_backwards
            `serialize32_nondep_then_backwards`
            serialize32_asn1_TLV_backwards_of_type BIT_STRING)
  (* f2 *) (synth_subjectPublicKeyInfo_ECDSA_P256_t)
  (* g1 *) (synth_subjectPublicKeyInfo_ECDSA_P256_t')
  (* g1'*) (synth_subjectPublicKeyInfo_ECDSA_P256_t')
  (* prf*) ()

let serialize32_subjectPublicKeyInfo_sequence_TLV_ECDSA_P256_backwards
: serializer32_backwards (serialize_subjectPublicKeyInfo_sequence_TLV_ECDSA_P256)
= serialize32_asn1_sequence_TLV_backwards
  (* ls *) (serialize32_subjectPublicKeyInfo_sequence_ECDSA_P256_backwards)
