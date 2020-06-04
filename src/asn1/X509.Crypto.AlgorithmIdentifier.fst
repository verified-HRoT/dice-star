module X509.Crypto.AlgorithmIdentifier

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

let algorithmIdentifier_t
  (alg: cryptoAlg)
= match alg with
  | ECDSA_P256 -> algorithmIdentifier_ECDSA_P256_t

private
let algorithmIdentifier_t'_aux
  (alg: cryptoAlg)
= match alg with
  | ECDSA_P256 -> tuple2 (datatype_of_asn1_type OID) (datatype_of_asn1_type OID)

/// tuple repr
let filter_algorithmIdentifier_t'
  (alg: cryptoAlg)
  (x': algorithmIdentifier_t'_aux alg)
: GTot bool
= match alg with
  | ECDSA_P256 -> ( let x' = x' <: tuple2 (datatype_of_asn1_type OID) (datatype_of_asn1_type OID) in
                    fst x' = OID_EC_ALG_UNRESTRICTED &&
                    snd x' = OID_EC_GRP_SECP256R1 )

let algorithmIdentifier_t'
  (alg: cryptoAlg)
= parse_filter_refine (filter_algorithmIdentifier_t' alg)

/// tuple repr -> record repr
let synth_algorithmIdentifier_t
  (alg: cryptoAlg)
  (x': algorithmIdentifier_t' alg)
: GTot (algorithmIdentifier_t alg)
= match alg with
  | ECDSA_P256 -> ( let x' = x' <: tuple2 (datatype_of_asn1_type OID) (datatype_of_asn1_type OID) in
                    { alg_id_oid_ecdsa = fst x';
                      alg_id_oid_p256  = snd x' } )

/// record repr -> tuple repr
let synth_algorithmIdentifier_t'
  (alg: cryptoAlg)
  (x: algorithmIdentifier_t alg)
: Tot (x': algorithmIdentifier_t' alg { x == synth_algorithmIdentifier_t alg x' })
= match alg with
  | ECDSA_P256 -> ( let x = x <: algorithmIdentifier_ECDSA_P256_t in
                    ((x.alg_id_oid_ecdsa <: datatype_of_asn1_type OID),
                     (x.alg_id_oid_p256  <: datatype_of_asn1_type OID)) )

/// sequence value (body) parser
let parse_algorithmIdentifier
  (alg: cryptoAlg)
: parser _ (algorithmIdentifier_t alg)
= match alg with
  | ECDSA_P256 -> ( parse_asn1_TLV_of_type OID
                    `nondep_then`
                    parse_asn1_TLV_of_type OID
                    `parse_filter`
                    filter_algorithmIdentifier_t' alg
                    `parse_synth`
                    synth_algorithmIdentifier_t alg )

/// sequence value serializer
let serialize_algorithmIdentifier
  (alg: cryptoAlg)
: serializer (parse_algorithmIdentifier alg)
= match alg with
  | ECDSA_P256 -> ( serialize_synth
                    (* p1 *) (parse_asn1_TLV_of_type OID
                              `nondep_then`
                              parse_asn1_TLV_of_type OID
                              `parse_filter`
                              filter_algorithmIdentifier_t' alg)
                    (* f2 *) (synth_algorithmIdentifier_t alg)
                    (* s1 *) (serialize_asn1_TLV_of_type OID
                              `serialize_nondep_then`
                              serialize_asn1_TLV_of_type OID
                              `serialize_filter`
                              filter_algorithmIdentifier_t' alg)
                    (* g1 *) (synth_algorithmIdentifier_t' alg)
                    (* prf*) () )

/// lemma: unfold sequence value serializer
let lemma_serialize_algorithmIdentifier_unfold
  (alg: cryptoAlg)
  (x: algorithmIdentifier_t alg)
: Lemma (
  match alg with
  | ECDSA_P256 -> ( serialize (serialize_algorithmIdentifier alg) x ==
                    serialize (serialize_asn1_TLV_of_type OID) x.alg_id_oid_ecdsa
                    `Seq.append`
                    serialize (serialize_asn1_TLV_of_type OID) x.alg_id_oid_p256 ))
= match alg with
  | ECDSA_P256 -> ( serialize_nondep_then_eq
                    (* s1 *) (serialize_asn1_TLV_of_type OID)
                    (* s2 *) (serialize_asn1_TLV_of_type OID)
                    (* in *) (synth_algorithmIdentifier_t' alg x);
                    serialize_synth_eq
                    (* p1 *) (parse_asn1_TLV_of_type OID
                              `nondep_then`
                              parse_asn1_TLV_of_type OID
                              `parse_filter`
                              filter_algorithmIdentifier_t' alg)
                    (* f2 *) (synth_algorithmIdentifier_t alg)
                    (* s1 *) (serialize_asn1_TLV_of_type OID
                              `serialize_nondep_then`
                              serialize_asn1_TLV_of_type OID
                              `serialize_filter`
                              filter_algorithmIdentifier_t' alg)
                    (* g1 *) (synth_algorithmIdentifier_t' alg)
                    (* prf*) ()
                    (* in *) x )

/// lemma: reveal sequence serialization size
let lemma_serialize_algorithmIdentifier_size
  (alg: cryptoAlg)
  (x: algorithmIdentifier_t alg)
: Lemma (
  match alg with
  | ECDSA_P256 -> ( Seq.length (serialize (serialize_algorithmIdentifier alg) x) ==
                    length_of_asn1_primitive_TLV x.alg_id_oid_ecdsa +
                    length_of_asn1_primitive_TLV x.alg_id_oid_p256 ))
= match alg with
  | ECDSA_P256 -> ( lemma_serialize_algorithmIdentifier_unfold alg x )

/// inbound record repr
let algorithmIdentifier_t_inbound
  (alg: cryptoAlg)
= match alg with
  | ECDSA_P256 -> inbound_sequence_value_of (serialize_algorithmIdentifier alg)

/// TLV
// unfold
let parse_algorithmIdentifier_sequence_TLV
  (alg: cryptoAlg)
: parser (parse_asn1_envelop_tag_with_TLV_kind SEQUENCE) (algorithmIdentifier_t_inbound alg)
= match alg with
  | ECDSA_P256 -> ( algorithmIdentifier_t_inbound alg
                    `coerce_parser`
                    parse_asn1_sequence_TLV (serialize_algorithmIdentifier alg) )

let serialize_algorithmIdentifier_sequence_TLV
  (alg: cryptoAlg)
: serializer (parse_algorithmIdentifier_sequence_TLV alg)
= match alg with
  | ECDSA_P256 -> ( serialize_asn1_sequence_TLV (serialize_algorithmIdentifier alg) )

let lemma_serialize_algorithmIdentifier_sequence_TLV_unfold
  (alg: cryptoAlg)
= match alg with
  | ECDSA_P256 -> ( lemma_serialize_asn1_envelop_tag_with_TLV_size SEQUENCE (serialize_algorithmIdentifier alg) )

let lemma_serialize_algorithmIdentifier_sequence_TLV_size
  (alg: cryptoAlg)
= match alg with
  | ECDSA_P256 -> ( lemma_serialize_asn1_envelop_tag_with_TLV_size SEQUENCE (serialize_algorithmIdentifier alg) )

/// Low
///

inline_for_extraction
let serialize32_algorithmIdentifier_backwards
  (alg: cryptoAlg)
: serializer32_backwards (serialize_algorithmIdentifier alg)
= match alg with
  | ECDSA_P256 -> ( serialize32_synth_backwards
                    (* ls *) (serialize32_asn1_TLV_backwards_of_type OID
                              `serialize32_nondep_then_backwards`
                              serialize32_asn1_TLV_backwards_of_type OID
                              `serialize32_filter_backwards`
                              filter_algorithmIdentifier_t' alg)
                    (* f2 *) (synth_algorithmIdentifier_t alg)
                    (* g1 *) (synth_algorithmIdentifier_t' alg)
                    (* g1'*) (synth_algorithmIdentifier_t' alg)
                    (* prf*) () )

let serialize32_algorithmIdentifier_sequence_TLV_backwards
  (alg: cryptoAlg)
: serializer32_backwards (serialize_algorithmIdentifier_sequence_TLV alg)
= match alg with
  | ECDSA_P256 -> ( serialize32_asn1_sequence_TLV_backwards
                    (* s32 *) (serialize32_algorithmIdentifier_backwards alg) )
