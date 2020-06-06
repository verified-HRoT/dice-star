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
type algorithmIdentifier_ECDSA_P256_t = {
  alg_id_oid_ecdsa: oid: datatype_of_asn1_type OID {oid == OID_EC_ALG_UNRESTRICTED};
  alg_id_oid_p256 : oid: datatype_of_asn1_type OID {oid == OID_EC_GRP_SECP256R1}
}

type algorithmIdentifier_Ed25519_t = {
  algID_ed25519: oid: datatype_of_asn1_type OID { oid == OID_ED25519 }
}

let algorithmIdentifier_t
  (alg: cryptoAlg)
= match alg with
  | ECDSA_P256 -> algorithmIdentifier_ECDSA_P256_t
  | ED25519    -> algorithmIdentifier_Ed25519_t

private
let algorithmIdentifier_t'_aux
  (alg: cryptoAlg)
= match alg with
  | ECDSA_P256 -> tuple2 (datatype_of_asn1_type OID) (datatype_of_asn1_type OID)
  | ED25519    -> datatype_of_asn1_type OID

/// tuple repr
let filter_algorithmIdentifier_t'
  (alg: cryptoAlg)
  (x': algorithmIdentifier_t'_aux alg)
: GTot bool
= match alg with
  | ECDSA_P256 -> ( let x' = x' <: tuple2 (datatype_of_asn1_type OID) (datatype_of_asn1_type OID) in
                    fst x' = OID_EC_ALG_UNRESTRICTED &&
                    snd x' = OID_EC_GRP_SECP256R1 )
  | ED25519    -> ( let x' = x'<: datatype_of_asn1_type OID in
                    x' = OID_ED25519 )

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
  | ED25519    -> ( let x' = x' <: datatype_of_asn1_type OID in
                    { algID_ed25519 = x' } )

/// record repr -> tuple repr
let synth_algorithmIdentifier_t'
  (alg: cryptoAlg)
  (x: algorithmIdentifier_t alg)
: Tot (x': algorithmIdentifier_t' alg { x == synth_algorithmIdentifier_t alg x' })
= match alg with
  | ECDSA_P256 -> ( let x = x <: algorithmIdentifier_ECDSA_P256_t in
                    ((x.alg_id_oid_ecdsa <: datatype_of_asn1_type OID),
                     (x.alg_id_oid_p256  <: datatype_of_asn1_type OID)) )
  | ED25519    -> ( let x = x<: algorithmIdentifier_Ed25519_t in
                    x.algID_ed25519 )

let parse_algorithmIdentifier_kind
  (alg: cryptoAlg)
: parser_kind
= match alg with
  | ECDSA_P256 -> ( parse_asn1_TLV_kind_of_type OID
                    `and_then_kind`
                    parse_asn1_TLV_kind_of_type OID )
  | ED25519    -> ( parse_asn1_TLV_kind_of_type OID )

/// sequence value (body) parser
let parse_algorithmIdentifier
  (alg: cryptoAlg)
: parser (parse_algorithmIdentifier_kind alg) (algorithmIdentifier_t alg)
= match alg with
  | ECDSA_P256 -> ( parse_asn1_TLV_of_type OID
                    `nondep_then`
                    parse_asn1_TLV_of_type OID
                    `parse_filter`
                    filter_algorithmIdentifier_t' alg
                    `parse_synth`
                    synth_algorithmIdentifier_t alg )
  | ED25519    -> ( parse_asn1_TLV_of_type OID
                    `parse_filter`
                    filter_algorithmIdentifier_t' alg
                    `parse_synth`
                    synth_algorithmIdentifier_t alg)

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

  | ED25519    -> ( serialize_synth
                    (* p1 *) (parse_asn1_TLV_of_type OID
                              `parse_filter`
                              filter_algorithmIdentifier_t' alg)
                    (* f2 *) (synth_algorithmIdentifier_t alg)
                    (* s1 *) (serialize_asn1_TLV_of_type OID
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
                    serialize (serialize_asn1_TLV_of_type OID) OID_EC_ALG_UNRESTRICTED
                    `Seq.append`
                    serialize (serialize_asn1_TLV_of_type OID) OID_EC_GRP_SECP256R1 )
  | ED25519    -> ( serialize (serialize_algorithmIdentifier alg) x ==
                    serialize (serialize_asn1_TLV_of_type OID) OID_ED25519 /\
                    length_of_opaque_serialization (serialize_algorithmIdentifier alg) x ==
                    5
                    ))
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
  | ED25519    -> ( serialize_synth_eq
                    (* p1 *) (parse_asn1_TLV_of_type OID
                              `parse_filter`
                              filter_algorithmIdentifier_t' alg)
                    (* f2 *) (synth_algorithmIdentifier_t alg)
                    (* s1 *) (serialize_asn1_TLV_of_type OID
                              `serialize_filter`
                              filter_algorithmIdentifier_t' alg)
                    (* g1 *) (synth_algorithmIdentifier_t' alg)
                    (* prf*) ()
                    (* in *) x;
                    assert_norm (length_of_asn1_primitive_TLV OID_ED25519 == 5) )

/// lemma: reveal sequence serialization size

#push-options "--query_stats"
let lemma_serialize_algorithmIdentifier_size
  (alg: cryptoAlg)
  (x: algorithmIdentifier_t alg)
: Lemma (
  match alg with (* FIXME *)
  // | ECDSA_P256 -> ( let x = x <: algorithmIdentifier_ECDSA_P256_t in
  //                   Seq.length (serialize (serialize_algorithmIdentifier alg) x) ==
  //                   length_of_asn1_primitive_TLV x.alg_id_oid_ecdsa +
  //                   length_of_asn1_primitive_TLV x.alg_id_oid_p256 )
  | ED25519    -> ( let x = x <: algorithmIdentifier_Ed25519_t in
                    Seq.length (serialize (serialize_algorithmIdentifier alg) x) ==
                    5 )
                    //length_of_asn1_primitive_TLV x.algID_ed25519 /\
                    //x.algID_ed25519 == OID_ED25519 )
                    //length_of_asn1_primitive_TLV x.algID_ed25519 == 5)
  | _ -> True)
= match alg with
  | ECDSA_P256 -> ( lemma_serialize_algorithmIdentifier_unfold alg x )
  | ED25519    -> ( lemma_serialize_algorithmIdentifier_unfold alg x;
                    assert_norm (length_of_asn1_primitive_TLV x.algID_ed25519 == 5 ))

/// inbound record repr
let algorithmIdentifier_t_inbound
  (alg: cryptoAlg)
= match alg with
  | ECDSA_P256 -> inbound_sequence_value_of (serialize_algorithmIdentifier alg)
  | ED25519    -> inbound_sequence_value_of (serialize_algorithmIdentifier alg)

/// TLV
// unfold
let parse_algorithmIdentifier_sequence_TLV
  (alg: cryptoAlg)
: parser (parse_asn1_envelop_tag_with_TLV_kind SEQUENCE) (algorithmIdentifier_t_inbound alg)
= match alg with
  | ECDSA_P256 -> ( //algorithmIdentifier_t_inbound alg
                    //`coerce_parser`
                    parse_asn1_sequence_TLV (serialize_algorithmIdentifier alg) )
  | ED25519    -> ( //algorithmIdentifier_t_inbound alg
                    //`coerce_parser`
                    parse_asn1_sequence_TLV (serialize_algorithmIdentifier alg) )

let serialize_algorithmIdentifier_sequence_TLV
  (alg: cryptoAlg)
: serializer (parse_algorithmIdentifier_sequence_TLV alg)
= match alg with
  | ECDSA_P256 -> ( serialize_asn1_sequence_TLV (serialize_algorithmIdentifier alg) )
  | ED25519    -> ( serialize_asn1_sequence_TLV (serialize_algorithmIdentifier alg) )

let lemma_serialize_algorithmIdentifier_sequence_TLV_unfold
  (alg: cryptoAlg)
  (x: algorithmIdentifier_t_inbound alg)
: Lemma ( prop_serialize_asn1_sequence_TLV_unfold (serialize_algorithmIdentifier alg) x )
= lemma_serialize_asn1_sequence_TLV_unfold (serialize_algorithmIdentifier alg) x

let lemma_serialize_algorithmIdentifier_sequence_TLV_size
  (alg: cryptoAlg)
  (x: algorithmIdentifier_t_inbound alg)
: Lemma ( prop_serialize_asn1_sequence_TLV_size (serialize_algorithmIdentifier alg) x )
= match alg with
  | ECDSA_P256 -> ( lemma_serialize_asn1_sequence_TLV_size (serialize_algorithmIdentifier alg) x )
  | ED25519    -> ( lemma_serialize_asn1_sequence_TLV_size (serialize_algorithmIdentifier alg) x )

#push-options "--query_stats --z3rlimit 32 --fuel 4 --ifuel 4"
let lemma_serialize_algorithmIdentifier_sequence_TLV_size_exact
  (alg: cryptoAlg {alg == ED25519})
  (x: algorithmIdentifier_t alg)
: Lemma (
  match alg with
  // | ECDSA_P256 -> ( length_of_opaque_serialization (serialize_algorithmIdentifier_sequence_TLV alg) x == 17 )
  | ED25519    -> ( lemma_serialize_algorithmIdentifier_size alg x;
                    length_of_opaque_serialization (serialize_algorithmIdentifier_sequence_TLV alg) x == 7 )
)
= match alg with
  | ED25519    -> ( lemma_serialize_algorithmIdentifier_size alg x;
                    lemma_serialize_asn1_sequence_TLV_unfold (serialize_algorithmIdentifier alg) x;
                    lemma_serialize_asn1_sequence_TLV_size   (serialize_algorithmIdentifier alg) x;
                    // lemma_serialize_algorithmIdentifier_size alg x;
                    assert_norm (length_of_TLV OID (length_of_opaque_serialization (serialize_algorithmIdentifier alg) x) == 7) )
#pop-options

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
  | ED25519    -> ( serialize32_synth_backwards
                    (* ls *) (serialize32_asn1_TLV_backwards_of_type OID
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
  | ED25519    -> ( serialize32_asn1_sequence_TLV_backwards
                    (* s32 *) (serialize32_algorithmIdentifier_backwards alg) )

(* helpers *)
let _ = assert (length_of_oid OID_EC_GRP_SECP256R1 == 6)

#push-options "--z3rlimit 4 --fuel 2 --ifuel 1"
noextract inline_for_extraction
let x509_get_algorithmIdentifier
  (alg: cryptoAlg {alg == ED25519})
: Tot (algorithmIdentifier_t_inbound alg)
=
  match alg with
  | ED25519 -> ( let algID: algorithmIdentifier_t alg = { algID_ed25519 = OID_ED25519 } in
                 (* Prf *) lemma_serialize_algorithmIdentifier_size alg algID;
                 (* Prf *) (**) lemma_serialize_asn1_oid_TLV_size algID.algID_ed25519;
                 (* return *) algID )
#pop-options

