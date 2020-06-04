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
noeq
type subjectPublicKeyInfo_t
  (alg: cryptoAlg)
= { subjectPubKey_alg : algorithmIdentifier_t_inbound alg;
    subjectPubKey     : datatype_of_asn1_type BIT_STRING }

/// tuple repr
let subjectPublicKeyInfo_t'
  (alg: cryptoAlg)
= tuple2
  (algorithmIdentifier_t_inbound alg)
  (datatype_of_asn1_type BIT_STRING)

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
  `parse_synth`
  synth_subjectPublicKeyInfo_t alg

let serialize_subjectPublicKeyInfo
  (alg: cryptoAlg)
: serializer (parse_subjectPublicKeyInfo alg)
= serialize_synth
  (* p1 *) (parse_algorithmIdentifier_sequence_TLV alg
            `nondep_then`
            parse_asn1_TLV_of_type BIT_STRING)
  (* f2 *) (synth_subjectPublicKeyInfo_t alg)
  (* s1 *) (serialize_algorithmIdentifier_sequence_TLV alg
            `serialize_nondep_then`
            serialize_asn1_TLV_of_type BIT_STRING)
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
            parse_asn1_TLV_of_type BIT_STRING)
  (* f2 *) (synth_subjectPublicKeyInfo_t alg)
  (* s1 *) (serialize_algorithmIdentifier_sequence_TLV alg
            `serialize_nondep_then`
            serialize_asn1_TLV_of_type BIT_STRING)
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
  // length_of_opaque_serialization (serialize_subjectPublicKeyInfo alg) x ==
  // length_of_opaque_serialization (serialize_algorithmIdentifier_sequence_TLV alg) x.subjectPubKey_alg +
  // length_of_opaque_serialization (serialize_asn1_TLV_of_type BIT_STRING) x.subjectPubKey
)
= lemma_serialize_subjectPublicKeyInfo_unfold alg x

(* NOTE: Define the `inbound` version of value type after we defined then serializer. *)
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
= lemma_serialize_asn1_sequence_TLV_unfold (serialize_subjectPublicKeyInfo alg)

let lemma_serialize_subjectPublicKeyInfo_sequence_TLV_size
  (alg: cryptoAlg)
= lemma_serialize_asn1_sequence_TLV_size (serialize_subjectPublicKeyInfo alg)

/// Low
///

inline_for_extraction
let serialize32_subjectPublicKeyInfo_backwards
  (alg: cryptoAlg)
: serializer32_backwards (serialize_subjectPublicKeyInfo alg)
= serialize32_synth_backwards
  (* ls *) (serialize32_algorithmIdentifier_sequence_TLV_backwards alg
            `serialize32_nondep_then_backwards`
            serialize32_asn1_TLV_backwards_of_type BIT_STRING)
  (* f2 *) (synth_subjectPublicKeyInfo_t alg)
  (* g1 *) (synth_subjectPublicKeyInfo_t' alg)
  (* g1'*) (synth_subjectPublicKeyInfo_t' alg)
  (* prf*) ()

let serialize32_subjectPublicKeyInfo_sequence_TLV_backwards
  (alg: cryptoAlg)
: serializer32_backwards (serialize_subjectPublicKeyInfo_sequence_TLV alg)
= serialize32_asn1_sequence_TLV_backwards
  (* ls *) (serialize32_subjectPublicKeyInfo_backwards alg)
