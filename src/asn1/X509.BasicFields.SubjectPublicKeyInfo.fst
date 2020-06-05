module X509.BasicFields.SubjectPublicKeyInfo

open LowParse.Low.Base
// open LowParse.Low.Combinators

open ASN1.Spec
open ASN1.Low

open X509.Base
open X509.Crypto

open FStar.Integers

(* SubjectPublicKeyInfo
  ======================
*)
/// Record repr
type subjectPublicKeyInfo_t
  (alg: cryptoAlg)
= { subjectPubKey_alg : algorithmIdentifier_t_inbound alg;
    subjectPubKey     : pubkey_t alg }

let filter_subjectPublicKeyInfo_t'
  (alg: cryptoAlg)
  (x: (algorithmIdentifier_t_inbound alg) `tuple2` (datatype_of_asn1_type BIT_STRING))
: GTot bool
= match alg with
  | ECDSA_P256 -> true
  | ED25519    -> (snd x).bs_len = 33ul &&
                  (snd x).bs_unused_bits = 0ul

/// tuple repr
unfold
let subjectPublicKeyInfo_t'
  (alg: cryptoAlg)
= parse_filter_refine (filter_subjectPublicKeyInfo_t' alg)

let synth_subjectPublicKeyInfo_t
  (alg: cryptoAlg)
  (x': subjectPublicKeyInfo_t' alg)
: GTot (subjectPublicKeyInfo_t alg)
= { subjectPubKey_alg = fst x';
    subjectPubKey     = snd x' }

let synth_subjectPublicKeyInfo_t'
  (alg: cryptoAlg)
  (x: subjectPublicKeyInfo_t alg)
: Tot (x': subjectPublicKeyInfo_t' alg { x == synth_subjectPublicKeyInfo_t alg x' })
= (x.subjectPubKey_alg , x.subjectPubKey)

let parse_subjectPublicKeyInfo
  (alg: cryptoAlg)
: parser _ (subjectPublicKeyInfo_t alg)
= parse_algorithmIdentifier_sequence_TLV alg
  `nondep_then`
  parse_asn1_TLV_of_type BIT_STRING
  `parse_filter`
  filter_subjectPublicKeyInfo_t' alg
  `parse_synth`
  synth_subjectPublicKeyInfo_t alg

let serialize_subjectPublicKeyInfo
  (alg: cryptoAlg)
: serializer (parse_subjectPublicKeyInfo alg)
= serialize_synth
  (* p1 *) (parse_algorithmIdentifier_sequence_TLV alg
            `nondep_then`
            parse_asn1_TLV_of_type BIT_STRING
            `parse_filter`
            filter_subjectPublicKeyInfo_t' alg)
  (* f2 *) (synth_subjectPublicKeyInfo_t alg)
  (* s1 *) (serialize_algorithmIdentifier_sequence_TLV alg
            `serialize_nondep_then`
            serialize_asn1_TLV_of_type BIT_STRING
            `serialize_filter`
            filter_subjectPublicKeyInfo_t' alg)
  (* g1 *) (synth_subjectPublicKeyInfo_t' alg)
  (* prf*) ()

let lemma_serialize_subjectPublicKeyInfo_unfold
  (alg: cryptoAlg)
  (x: subjectPublicKeyInfo_t alg)
: Lemma (
  serialize (serialize_subjectPublicKeyInfo alg) x ==
  serialize (serialize_algorithmIdentifier_sequence_TLV alg) x.subjectPubKey_alg
  `Seq.append`
  serialize (serialize_asn1_TLV_of_type BIT_STRING) x.subjectPubKey
)
= serialize_nondep_then_eq
  (* s1 *) (serialize_algorithmIdentifier_sequence_TLV alg)
  (* s2 *) (serialize_asn1_TLV_of_type BIT_STRING)
  (* in *) (synth_subjectPublicKeyInfo_t' alg x);
  serialize_synth_eq
  (* p1 *) (parse_algorithmIdentifier_sequence_TLV alg
            `nondep_then`
            parse_asn1_TLV_of_type BIT_STRING
            `parse_filter`
            filter_subjectPublicKeyInfo_t' alg)
  (* f2 *) (synth_subjectPublicKeyInfo_t alg)
  (* s1 *) (serialize_algorithmIdentifier_sequence_TLV alg
            `serialize_nondep_then`
            serialize_asn1_TLV_of_type BIT_STRING
            `serialize_filter`
            filter_subjectPublicKeyInfo_t' alg)
  (* g1 *) (synth_subjectPublicKeyInfo_t' alg)
  (* prf*) ()
  (* in *) x

let lemma_serialize_subjectPublicKeyInfo_size
  (alg: cryptoAlg)
  (x: subjectPublicKeyInfo_t alg)
: Lemma (
  Seq.length (serialize (serialize_subjectPublicKeyInfo alg) x) ==
  Seq.length (serialize (serialize_algorithmIdentifier_sequence_TLV alg) x.subjectPubKey_alg) +
  Seq.length (serialize (serialize_asn1_TLV_of_type BIT_STRING) x.subjectPubKey)
)
= lemma_serialize_subjectPublicKeyInfo_unfold alg x

let subjectPublicKeyInfo_t_inbound
  (alg: cryptoAlg)
= inbound_sequence_value_of (serialize_subjectPublicKeyInfo alg)

/// TLV
///
let parse_subjectPublicKeyInfo_sequence_TLV
  (alg: cryptoAlg)
: parser _ (subjectPublicKeyInfo_t_inbound alg)
= parse_asn1_sequence_TLV (serialize_subjectPublicKeyInfo alg)

let serialize_subjectPublicKeyInfo_sequence_TLV
  (alg: cryptoAlg)
: serializer (parse_subjectPublicKeyInfo_sequence_TLV alg)
= serialize_asn1_sequence_TLV (serialize_subjectPublicKeyInfo alg)

let lemma_serialize_subjectPublicKeyInfo_sequence_TLV_unfold
  (alg: cryptoAlg)
  (x: subjectPublicKeyInfo_t_inbound alg)
: Lemma ( prop_serialize_asn1_sequence_TLV_unfold (serialize_subjectPublicKeyInfo alg) x )
= lemma_serialize_asn1_sequence_TLV_unfold (serialize_subjectPublicKeyInfo alg) x

let lemma_serialize_subjectPublicKeyInfo_sequence_TLV_size
  (alg: cryptoAlg)
  (x: subjectPublicKeyInfo_t_inbound alg)
: Lemma ( prop_serialize_asn1_sequence_TLV_size (serialize_subjectPublicKeyInfo alg) x )
= lemma_serialize_asn1_sequence_TLV_size (serialize_subjectPublicKeyInfo alg) x

let lemma_serialize_subjectPublicKeyInfo_sequence_TLV_size_exact
  (alg: cryptoAlg {alg == ED25519})
  (x: subjectPublicKeyInfo_t_inbound alg)
: Lemma (
  match alg with
  | ED25519   -> ( length_of_opaque_serialization (serialize_subjectPublicKeyInfo_sequence_TLV alg) x == 44 )
)
= admit()
  // match alg with
  // | ED25519   -> ( lemma_serialize_subjectPublicKeyInfo_sequence_TLV_unfold alg x;
  //                  lemma_serialize_subjectPublicKeyInfo_sequence_TLV_size   alg x;
  //                    lemma_serialize_subjectPublicKeyInfo_size alg x;
  //                    (**) lemma_serialize_algorithmIdentifier_sequence_TLV_size_exact alg x.subjectPubKey_alg;
  //                  // assume ( let bs: pubkey_t ED25519 = x.subjectPubKey in
  //                  //          length_of_asn1_primitive_TLV bs == 35 );
  //                  admit() )

/// Low
///

inline_for_extraction
let serialize32_subjectPublicKeyInfo_backwards
  (alg: cryptoAlg)
: serializer32_backwards (serialize_subjectPublicKeyInfo alg)
= serialize32_synth_backwards
  (* ls *) (serialize32_algorithmIdentifier_sequence_TLV_backwards alg
            `serialize32_nondep_then_backwards`
            serialize32_asn1_TLV_backwards_of_type BIT_STRING
            `serialize32_filter_backwards`
            filter_subjectPublicKeyInfo_t' alg)
  (* f2 *) (synth_subjectPublicKeyInfo_t alg)
  (* g1 *) (synth_subjectPublicKeyInfo_t' alg)
  (* g1'*) (synth_subjectPublicKeyInfo_t' alg)
  (* prf*) ()

let serialize32_subjectPublicKeyInfo_sequence_TLV_backwards
  (alg: cryptoAlg)
: serializer32_backwards (serialize_subjectPublicKeyInfo_sequence_TLV alg)
= serialize32_asn1_sequence_TLV_backwards
  (* ls *) (serialize32_subjectPublicKeyInfo_backwards alg)
