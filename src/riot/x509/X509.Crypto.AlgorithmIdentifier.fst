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

let algorithmIdentifier_payload_t
  // (alg: supported_crypto_alg_t)
= algorithmIdentifier_Ed25519_t
  // match alg with
  // | AlgID_ECDSA_P256 -> algorithmIdentifier_ECDSA_P256_t
  // | AlgID_Ed25519    -> algorithmIdentifier_Ed25519_t

let algorithmIdentifier_payload_t'_aux
  // (alg: supported_crypto_alg_t)
=
  // match alg with
  // | AlgID_ECDSA_P256 -> tuple2 (datatype_of_asn1_type OID) (datatype_of_asn1_type OID)
  // | AlgID_Ed25519    ->
  datatype_of_asn1_type OID

/// tuple repr
let filter_algorithmIdentifier_payload_t'
  // (alg: supported_crypto_alg_t)
  (x': algorithmIdentifier_payload_t'_aux)
: GTot bool
=
  // match alg with
  // | AlgID_ECDSA_P256 -> ( let x' = x' <: tuple2 (datatype_of_asn1_type OID) (datatype_of_asn1_type OID) in
  //                   fst x' = OID_EC_ALG_UNRESTRICTED &&
  //                   snd x' = OID_EC_GRP_SECP256R1 )
  // | AlgID_Ed25519    ->
  ( let x' = x'<: datatype_of_asn1_type OID in
                    x' = OID_ED25519 )

let algorithmIdentifier_payload_t'
  // (alg: supported_crypto_alg_t)
= parse_filter_refine (filter_algorithmIdentifier_payload_t')

/// tuple repr -> record repr
let synth_algorithmIdentifier_payload_t
  // (alg: supported_crypto_alg_t)
  (x': algorithmIdentifier_payload_t')
: GTot (algorithmIdentifier_payload_t)
=
  // match alg with
  // | AlgID_ECDSA_P256 -> ( let x' = x' <: tuple2 (datatype_of_asn1_type OID) (datatype_of_asn1_type OID) in
  //                   { alg_id_oid_ecdsa = fst x';
  //                     alg_id_oid_p256  = snd x' } )
  // | AlgID_Ed25519    ->
  ( let x' = x' <: datatype_of_asn1_type OID in
                    { algID_ed25519 = x' } )

/// record repr -> tuple repr

inline_for_extraction noextract
let synth_algorithmIdentifier_payload_t'
  // (alg: supported_crypto_alg_t)
  (x: algorithmIdentifier_payload_t)
: Tot (x': algorithmIdentifier_payload_t' { x == synth_algorithmIdentifier_payload_t x' })
=
  // match alg with
  // | AlgID_ECDSA_P256 -> ( let x = x <: algorithmIdentifier_ECDSA_P256_t in
  //                   ((x.alg_id_oid_ecdsa <: datatype_of_asn1_type OID),
  //                    (x.alg_id_oid_p256  <: datatype_of_asn1_type OID)) )
  // | AlgID_Ed25519    ->
  ( let x = x<: algorithmIdentifier_Ed25519_t in
                    x.algID_ed25519 )

let parse_algorithmIdentifier_payload_kind
  // (alg: supported_crypto_alg_t)
: parser_kind
=
  // match alg with
  // | AlgID_ECDSA_P256 -> ( parse_asn1_TLV_kind_of_type OID
  //                   `and_then_kind`
  //                   parse_asn1_TLV_kind_of_type OID )
  // | AlgID_Ed25519    ->
  ( parse_asn1_TLV_kind_of_type OID )

/// sequence value (body) parser
let parse_algorithmIdentifier_payload
  // (alg: supported_crypto_alg_t)
: parser (parse_algorithmIdentifier_payload_kind) (algorithmIdentifier_payload_t)
=
  // match alg with
  // | AlgID_ECDSA_P256 -> ( parse_asn1_TLV_of_type OID
  //                   `nondep_then`
  //                   parse_asn1_TLV_of_type OID
  //                   `parse_filter`
  //                   filter_algorithmIdentifier_payload_t' alg
  //                   `parse_synth`
  //                   synth_algorithmIdentifier_payload_t alg )
  // | AlgID_Ed25519    ->
  ( parse_asn1_TLV_of_type OID
                    `parse_filter`
                    filter_algorithmIdentifier_payload_t'
                    `parse_synth`
                    synth_algorithmIdentifier_payload_t)

/// sequence value serializer
let serialize_algorithmIdentifier_payload
  // (alg: supported_crypto_alg_t)
: serializer (parse_algorithmIdentifier_payload)
=
  // match alg with
  // | AlgID_ECDSA_P256 -> ( serialize_synth
  //                   (* p1 *) (parse_asn1_TLV_of_type OID
  //                             `nondep_then`
  //                             parse_asn1_TLV_of_type OID
  //                             `parse_filter`
  //                             filter_algorithmIdentifier_payload_t' alg)
  //                   (* f2 *) (synth_algorithmIdentifier_payload_t alg)
  //                   (* s1 *) (serialize_asn1_TLV_of_type OID
  //                             `serialize_nondep_then`
  //                             serialize_asn1_TLV_of_type OID
  //                             `serialize_filter`
  //                             filter_algorithmIdentifier_payload_t' alg)
  //                   (* g1 *) (synth_algorithmIdentifier_payload_t' alg)
  //                   (* prf*) () )

  // | AlgID_Ed25519    ->
                           ( serialize_synth
                    (* p1 *) (parse_asn1_TLV_of_type OID
                              `parse_filter`
                              filter_algorithmIdentifier_payload_t')
                    (* f2 *) (synth_algorithmIdentifier_payload_t)
                    (* s1 *) (serialize_asn1_TLV_of_type OID
                              `serialize_filter`
                              filter_algorithmIdentifier_payload_t')
                    (* g1 *) (synth_algorithmIdentifier_payload_t')
                    (* prf*) () )

/// lemma: unfold sequence value serializer
let lemma_serialize_algorithmIdentifier_payload_unfold
  // (alg: supported_crypto_alg_t)
  (x: algorithmIdentifier_payload_t)
: Lemma (
  // match alg with
  // | AlgID_ECDSA_P256 -> ( serialize (serialize_algorithmIdentifier alg) x ==
  //                   serialize (serialize_asn1_TLV_of_type OID) OID_EC_ALG_UNRESTRICTED
  //                   `Seq.append`
  //                   serialize (serialize_asn1_TLV_of_type OID) OID_EC_GRP_SECP256R1 )
  // | AlgID_Ed25519    ->
                   ( serialize (serialize_algorithmIdentifier_payload) x ==
                    serialize (serialize_asn1_TLV_of_type OID) OID_ED25519 /\
                    length_of_opaque_serialization (serialize_algorithmIdentifier_payload) x ==
                    5
                    ))
=
  // match alg with
  // | AlgID_ECDSA_P256 -> ( serialize_nondep_then_eq
  //                   (* s1 *) (serialize_asn1_TLV_of_type OID)
  //                   (* s2 *) (serialize_asn1_TLV_of_type OID)
  //                   (* in *) (synth_algorithmIdentifier_payload_t' alg x);
  //                   serialize_synth_eq
  //                   (* p1 *) (parse_asn1_TLV_of_type OID
  //                             `nondep_then`
  //                             parse_asn1_TLV_of_type OID
  //                             `parse_filter`
  //                             filter_algorithmIdentifier_payload_t' alg)
  //                   (* f2 *) (synth_algorithmIdentifier_payload_t alg)
  //                   (* s1 *) (serialize_asn1_TLV_of_type OID
  //                             `serialize_nondep_then`
  //                             serialize_asn1_TLV_of_type OID
  //                             `serialize_filter`
  //                             filter_algorithmIdentifier_payload_t' alg)
  //                   (* g1 *) (synth_algorithmIdentifier_payload_t' alg)
  //                   (* prf*) ()
  //                   (* in *) x )
  // | AlgID_Ed25519    ->
                          ( serialize_synth_eq
                    (* p1 *) (parse_asn1_TLV_of_type OID
                              `parse_filter`
                              filter_algorithmIdentifier_payload_t')
                    (* f2 *) (synth_algorithmIdentifier_payload_t)
                    (* s1 *) (serialize_asn1_TLV_of_type OID
                              `serialize_filter`
                              filter_algorithmIdentifier_payload_t')
                    (* g1 *) (synth_algorithmIdentifier_payload_t')
                    (* prf*) ()
                    (* in *) x;
                    assert_norm (length_of_asn1_primitive_TLV OID_ED25519 == 5) )

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
  // (alg: supported_crypto_alg_t)
  (x: algorithmIdentifier_payload_t)
: Lemma (
  // match alg with
  // | AlgID_ECDSA_P256 -> ( let x = x <: algorithmIdentifier_ECDSA_P256_t in
  //                   Seq.length (serialize (serialize_algorithmIdentifier alg) x) ==
  //                   length_of_asn1_primitive_TLV x.alg_id_oid_ecdsa +
  //                   length_of_asn1_primitive_TLV x.alg_id_oid_p256 )
  // | AlgID_Ed25519    ->
                   ( let x = x <: algorithmIdentifier_Ed25519_t in
                     length_of_opaque_serialization (serialize_algorithmIdentifier_payload) x
                     == length_of_algorithmIdentifier_payload () )
                    //length_of_asn1_primitive_TLV x.algID_ed25519 /\
                    //x.algID_ed25519 == OID_ED25519 )
                    //length_of_asn1_primitive_TLV x.algID_ed25519 == 5)
)
=
  // match alg with
  // | AlgID_ECDSA_P256 -> ( lemma_serialize_algorithmIdentifier_unfold alg x )
  // | AlgID_Ed25519    ->
                        ( lemma_serialize_algorithmIdentifier_payload_unfold x;
                    assert_norm (length_of_asn1_primitive_TLV x.algID_ed25519 == 5 ))

/// inbound record repr
let algorithmIdentifier_t
  // (alg: supported_crypto_alg_t)
=
  // match alg with
  // | AlgID_ECDSA_P256 -> inbound_sequence_value_of (serialize_algorithmIdentifier alg)
  // | AlgID_Ed25519    ->
  inbound_sequence_value_of (serialize_algorithmIdentifier_payload)

/// TLV
// unfold
let parse_algorithmIdentifier
  // (alg: supported_crypto_alg_t)
: parser (parse_asn1_envelop_tag_with_TLV_kind SEQUENCE) (algorithmIdentifier_t)
=
  // match alg with
  // | AlgID_ECDSA_P256 -> ( //algorithmIdentifier_t alg
  //                   //`coerce_parser`
  //                   parse_asn1_sequence_TLV (serialize_algorithmIdentifier alg) )
  // | AlgID_Ed25519    -> ( //algorithmIdentifier_t alg
                    //`coerce_parser`
                    parse_asn1_sequence_TLV (serialize_algorithmIdentifier_payload)

let serialize_algorithmIdentifier
  // (alg: supported_crypto_alg_t)
: serializer (parse_algorithmIdentifier)
=
  // match alg with
  // | AlgID_ECDSA_P256 -> ( serialize_asn1_sequence_TLV (serialize_algorithmIdentifier alg) )
  // | AlgID_Ed25519    ->
  ( serialize_asn1_sequence_TLV (serialize_algorithmIdentifier_payload) )

let lemma_serialize_algorithmIdentifier_unfold
  // (alg: supported_crypto_alg_t)
  (x: algorithmIdentifier_t)
: Lemma ( predicate_serialize_asn1_sequence_TLV_unfold (serialize_algorithmIdentifier_payload) x )
= lemma_serialize_asn1_sequence_TLV_unfold (serialize_algorithmIdentifier_payload) x

let lemma_serialize_algorithmIdentifier_size
  // (alg: supported_crypto_alg_t)
  (x: algorithmIdentifier_t)
: Lemma ( predicate_serialize_asn1_sequence_TLV_size (serialize_algorithmIdentifier_payload) x )
=
  // match alg with
  // | AlgID_ECDSA_P256 -> ( lemma_serialize_asn1_sequence_TLV_size (serialize_algorithmIdentifier alg) x )
  // | AlgID_Ed25519    ->
  ( lemma_serialize_asn1_sequence_TLV_size (serialize_algorithmIdentifier_payload) x )

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
  // match alg with
  // | AlgID_ECDSA_P256 -> ( length_of_opaque_serialization (serialize_algorithmIdentifier alg) x == 17 )
  // | AlgID_Ed25519    ->
                   ( lemma_serialize_algorithmIdentifier_payload_size x;
                     length_of_opaque_serialization (serialize_algorithmIdentifier) x
                     == length_of_algorithmIdentifier () )
)
=
  // match alg with
  // | AlgID_Ed25519    ->
                  ( lemma_serialize_algorithmIdentifier_payload_size x;
                    lemma_serialize_asn1_sequence_TLV_unfold (serialize_algorithmIdentifier_payload) x;
                    lemma_serialize_asn1_sequence_TLV_size   (serialize_algorithmIdentifier_payload) x;
                    // lemma_serialize_algorithmIdentifier_size alg x;
                    assert (length_of_TLV OID (length_of_opaque_serialization (serialize_algorithmIdentifier_payload) x) == 7) )
#pop-options

/// Low
///

inline_for_extraction
let serialize32_algorithmIdentifier_payload_backwards
  // (alg: supported_crypto_alg_t)
: serializer32_backwards (serialize_algorithmIdentifier_payload)
=
  // match alg with
  // | AlgID_ECDSA_P256 -> ( serialize32_synth_backwards
  //                   (* ls *) (serialize32_asn1_TLV_backwards_of_type OID
  //                             `serialize32_nondep_then_backwards`
  //                             serialize32_asn1_TLV_backwards_of_type OID
  //                             `serialize32_filter_backwards`
  //                             filter_algorithmIdentifier_t' alg)
  //                   (* f2 *) (synth_algorithmIdentifier_t alg)
  //                   (* g1 *) (synth_algorithmIdentifier_t' alg)
  //                   (* g1'*) (synth_algorithmIdentifier_t' alg)
  //                   (* prf*) () )
  // | AlgID_Ed25519    ->
                       ( serialize32_synth_backwards
                    (* ls *) (serialize32_asn1_TLV_backwards_of_type OID
                              `serialize32_filter_backwards`
                              filter_algorithmIdentifier_payload_t')
                    (* f2 *) (synth_algorithmIdentifier_payload_t)
                    (* g1 *) (synth_algorithmIdentifier_payload_t')
                    (* g1'*) (synth_algorithmIdentifier_payload_t')
                    (* prf*) () )

inline_for_extraction
let serialize32_algorithmIdentifier_backwards
  // (alg: supported_crypto_alg_t)
: serializer32_backwards (serialize_algorithmIdentifier)
=
  // match alg with
  // | AlgID_ECDSA_P256 -> ( serialize32_asn1_sequence_TLV_backwards
  //                   (* s32 *) (serialize32_algorithmIdentifier_backwards alg) )
  // | AlgID_Ed25519    ->
                        ( serialize32_asn1_sequence_TLV_backwards
                    (* s32 *) (serialize32_algorithmIdentifier_payload_backwards) )

(* helpers *)

#push-options "--z3rlimit 4 --fuel 0 --ifuel 0"
noextract inline_for_extraction
let x509_get_algorithmIdentifier ()
  // (alg: supported_crypto_alg_t {alg == AlgID_Ed25519})
: Tot (algorithmIdentifier_t)
=
  // match alg with
  // | AlgID_Ed25519 ->
                   ( let algID: algorithmIdentifier_payload_t = { algID_ed25519 = OID_ED25519 } in
                 (* Prf *) lemma_serialize_algorithmIdentifier_payload_size algID;
                 (* Prf *) (**) lemma_serialize_asn1_oid_TLV_size algID.algID_ed25519;
                 (* return *) algID )
#pop-options

