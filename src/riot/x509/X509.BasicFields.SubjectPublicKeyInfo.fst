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

//inline_for_extraction
type subjectPublicKeyInfo_payload_t
  // (alg: supported_crypto_alg_t)
= { subjectPubKey_alg : algorithmIdentifier_t;
    subjectPubKey     : pubkey_t }

let filter_subjectPublicKeyInfo_payload_t'
  // (alg: supported_crypto_alg_t)
  (x: (algorithmIdentifier_t) `tuple2` (datatype_of_asn1_type BIT_STRING))
: GTot bool
=
  // match alg with
  // | AlgID_ECDSA_P256 -> true
  // | AlgID_Ed25519    ->
  (snd x).bs_len = 33ul &&
  (snd x).bs_unused_bits = 0ul

/// tuple repr

unfold
let subjectPublicKeyInfo_payload_t'
  // (alg: supported_crypto_alg_t)
= parse_filter_refine (filter_subjectPublicKeyInfo_payload_t')

let synth_subjectPublicKeyInfo_payload_t
  // (alg: supported_crypto_alg_t)
  (x': subjectPublicKeyInfo_payload_t')
: GTot (subjectPublicKeyInfo_payload_t)
= { subjectPubKey_alg = fst x';
    subjectPubKey     = snd x' }


let synth_subjectPublicKeyInfo_payload_t'
  // (alg: supported_crypto_alg_t)
  (x: subjectPublicKeyInfo_payload_t)
: Tot (x': subjectPublicKeyInfo_payload_t' { x == synth_subjectPublicKeyInfo_payload_t x' })
= (x.subjectPubKey_alg , x.subjectPubKey)

let parse_subjectPublicKeyInfo_payload
  // (alg: supported_crypto_alg_t)
: parser _ (subjectPublicKeyInfo_payload_t)
= parse_algorithmIdentifier
  `nondep_then`
  parse_asn1_TLV_of_type BIT_STRING
  `parse_filter`
  filter_subjectPublicKeyInfo_payload_t'
  `parse_synth`
  synth_subjectPublicKeyInfo_payload_t

let serialize_subjectPublicKeyInfo_payload
  // (alg: supported_crypto_alg_t)
: serializer (parse_subjectPublicKeyInfo_payload)
= serialize_synth
  (* p1 *) (parse_algorithmIdentifier
            `nondep_then`
            parse_asn1_TLV_of_type BIT_STRING
            `parse_filter`
            filter_subjectPublicKeyInfo_payload_t')
  (* f2 *) (synth_subjectPublicKeyInfo_payload_t)
  (* s1 *) (serialize_algorithmIdentifier
            `serialize_nondep_then`
            serialize_asn1_TLV_of_type BIT_STRING
            `serialize_filter`
            filter_subjectPublicKeyInfo_payload_t')
  (* g1 *) (synth_subjectPublicKeyInfo_payload_t')
  (* prf*) ()

let lemma_serialize_subjectPublicKeyInfo_payload_unfold
  // (alg: supported_crypto_alg_t)
  (x: subjectPublicKeyInfo_payload_t)
: Lemma (
  serialize (serialize_subjectPublicKeyInfo_payload) x ==
  serialize (serialize_algorithmIdentifier) x.subjectPubKey_alg
  `Seq.append`
  serialize (serialize_asn1_TLV_of_type BIT_STRING) x.subjectPubKey
)
= serialize_nondep_then_eq
  (* s1 *) (serialize_algorithmIdentifier)
  (* s2 *) (serialize_asn1_TLV_of_type BIT_STRING)
  (* in *) (synth_subjectPublicKeyInfo_payload_t' x);
  serialize_synth_eq
  (* p1 *) (parse_algorithmIdentifier
            `nondep_then`
            parse_asn1_TLV_of_type BIT_STRING
            `parse_filter`
            filter_subjectPublicKeyInfo_payload_t')
  (* f2 *) (synth_subjectPublicKeyInfo_payload_t)
  (* s1 *) (serialize_algorithmIdentifier
            `serialize_nondep_then`
            serialize_asn1_TLV_of_type BIT_STRING
            `serialize_filter`
            filter_subjectPublicKeyInfo_payload_t')
  (* g1 *) (synth_subjectPublicKeyInfo_payload_t')
  (* prf*) ()
  (* in *) x

let lemma_serialize_subjectPublicKeyInfo_payload_size
  // (alg: supported_crypto_alg_t)
  (x: subjectPublicKeyInfo_payload_t)
: Lemma (
  Seq.length (serialize (serialize_subjectPublicKeyInfo_payload) x) ==
  Seq.length (serialize (serialize_algorithmIdentifier) x.subjectPubKey_alg) +
  Seq.length (serialize (serialize_asn1_TLV_of_type BIT_STRING) x.subjectPubKey)
)
= lemma_serialize_subjectPublicKeyInfo_payload_unfold x

let subjectPublicKeyInfo_t
  // (alg: supported_crypto_alg_t)
= inbound_sequence_value_of (serialize_subjectPublicKeyInfo_payload)

/// TLV
///
let parse_subjectPublicKeyInfo
  // (alg: supported_crypto_alg_t)
// : parser _ (subjectPublicKeyInfo_t)
=
  subjectPublicKeyInfo_t
  `coerce_parser`
  parse_asn1_sequence_TLV (serialize_subjectPublicKeyInfo_payload)

let serialize_subjectPublicKeyInfo
  // (alg: supported_crypto_alg_t)
// : serializer (parse_subjectPublicKeyInfo)
= coerce_parser_serializer
    parse_subjectPublicKeyInfo
    (serialize_asn1_sequence_TLV (serialize_subjectPublicKeyInfo_payload))
    ()

let lemma_serialize_subjectPublicKeyInfo_unfold
  // (alg: supported_crypto_alg_t)
  (x: subjectPublicKeyInfo_t)
: Lemma ( predicate_serialize_asn1_sequence_TLV_unfold (serialize_subjectPublicKeyInfo_payload) x )
= lemma_serialize_asn1_sequence_TLV_unfold (serialize_subjectPublicKeyInfo_payload) x

let lemma_serialize_subjectPublicKeyInfo_size
  // (alg: supported_crypto_alg_t)
  (x: subjectPublicKeyInfo_t)
: Lemma ( predicate_serialize_asn1_sequence_TLV_size (serialize_subjectPublicKeyInfo_payload) x )
= lemma_serialize_asn1_sequence_TLV_size (serialize_subjectPublicKeyInfo_payload) x

(* NOTE: For a subjectPublicKeyInfo for Ed25519, it consists
         1) a 1-byte tag
         2) a 1-byte length (the value field's length can be represented by 1 byte)
         3) a 7-byte algorithmIdentifier for Ed25519, whose length has been proved is 7,
            see `lemma_serialize_algorithmIdentifier_size_exact`
         4) a 35-byte bit string TLV (1 byte for tag, 1 byte for length, 33 bytes for a 32-byte bit string),
            see `length_of_asn1_primitive_value` (without tag and length) and `length_of_asn1_primitive_TLV`
            for the length calc.
         Thus the total length should be 1 + 1 + 7 + 35 = 44 bytes.
   NOTE: For the use of lemmas:
         For primitive types
         1) lemma_serialize_..._unfold will reveal one level of the serialization.
            For example, `lemma_serialize_asn1_bit_string_TLV_unfold bs` proves
            that serialization of bs's TLV == serialization of tag appends serialization
            of length appends serialization of value (the bs)
         2) lemma_serialize_..._size will reveal the size of a TLV equals to the sum of
            the serializations of Tag, Length and Value
         For SEQUENCE, which takes a serializer `s` of the SEQUENCE body, envelops it as
         a SEQUENCE TLV `lemma_serialize_...sequence_TLV_unfold/size` reveals this level
         of SEQUENCE "envelop".
*)

let length_of_subjectPublicKeyInfo
: asn1_TLV_length_of_type SEQUENCE
= 44

let len_of_subjectPublicKeyInfo
: (len: asn1_TLV_int32_of_type SEQUENCE
        { v len == length_of_subjectPublicKeyInfo })
= 44ul

#push-options "--z3rlimit 32 --fuel 0 --ifuel 0"
let lemma_serialize_subjectPublicKeyInfo_size_exact
  // (alg: supported_crypto_alg_t {alg == AlgID_Ed25519})
  (x: subjectPublicKeyInfo_t)
: Lemma (
  // match alg with
  // | AlgID_Ed25519   ->
  ( length_of_opaque_serialization (serialize_subjectPublicKeyInfo) x
    == length_of_subjectPublicKeyInfo )
)
=
  // match alg with
  // | AlgID_Ed25519   ->
                     ( (* reveal the SEQUENCE envelop *)
                   lemma_serialize_subjectPublicKeyInfo_unfold x;
                   lemma_serialize_subjectPublicKeyInfo_size   x;
                     (* reveal the SEQUENCE body *)
                     lemma_serialize_subjectPublicKeyInfo_payload_size x;
                     (**) lemma_serialize_algorithmIdentifier_size_exact x.subjectPubKey_alg;
                     assert ( let bs: pubkey_t = x.subjectPubKey in
                              length_of_asn1_primitive_TLV bs == 35 );
                     () )
#pop-options

/// Low
///

inline_for_extraction
let serialize32_subjectPublicKeyInfo_payload_backwards
  // (alg: supported_crypto_alg_t)
: serializer32_backwards (serialize_subjectPublicKeyInfo_payload)
= serialize32_synth_backwards
  (* ls *) (serialize32_algorithmIdentifier_backwards
            `serialize32_nondep_then_backwards`
            serialize32_asn1_TLV_backwards_of_type BIT_STRING
            `serialize32_filter_backwards`
            filter_subjectPublicKeyInfo_payload_t')
  (* f2 *) (synth_subjectPublicKeyInfo_payload_t)
  (* g1 *) (synth_subjectPublicKeyInfo_payload_t')
  (* g1'*) (synth_subjectPublicKeyInfo_payload_t')
  (* prf*) ()

inline_for_extraction
let serialize32_subjectPublicKeyInfo_backwards
  // (alg: supported_crypto_alg_t)
: serializer32_backwards (serialize_subjectPublicKeyInfo)
= coerce_serializer32_backwards
    (serialize_subjectPublicKeyInfo)
    (serialize32_asn1_sequence_TLV_backwards
     (* ls *) (serialize32_subjectPublicKeyInfo_payload_backwards))
    ()
(* helpers *)

module B32 = FStar.Bytes
open X509.Crypto.AlgorithmIdentifier
let subjectPublicKeyInfo_raw_t
  // (alg: supported_crypto_alg_t{alg == AlgID_Ed25519})
=
  // match alg with
  // | AlgID_Ed25519   ->
  B32.lbytes32 32ul

#push-options "--z3rlimit 16 --fuel 0 --ifuel 0"
let x509_get_subjectPublicKeyInfo
  // (pubkey_alg: supported_crypto_alg_t {pubkey_alg == AlgID_Ed25519} )
  (pubkey: B32.lbytes32 32ul)
: Tot (subjectPublicKeyInfo_t)
=
  lemma_trivial_bit_string_is_valid 33ul pubkey;
  let pubkey_bs: pubkey_t  = Mkbit_string_t 33ul 0ul pubkey in

  // if (pubkey_alg = AlgID_Ed25519) then
  ( let alg_id: algorithmIdentifier_t = x509_get_algorithmIdentifier () in
    (* Prf *) lemma_serialize_algorithmIdentifier_size_exact alg_id;

    let aliasPublicKeyInfo: subjectPublicKeyInfo_payload_t = {
       subjectPubKey_alg = alg_id;
       subjectPubKey     = pubkey_bs
    } in
    (* Prf *) lemma_serialize_subjectPublicKeyInfo_payload_size aliasPublicKeyInfo;
    (* Prf *) (**) lemma_serialize_asn1_bit_string_TLV_size aliasPublicKeyInfo.subjectPubKey;

    (* return *) aliasPublicKeyInfo )
  // else
  // ( false_elim() )
#pop-options