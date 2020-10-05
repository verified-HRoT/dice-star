module X509.BasicFields.SubjectPublicKeyInfo

open LowParse.Low.Base

open ASN1.Spec
open ASN1.Low

open X509.Base
open X509.Crypto

open FStar.Integers

type subjectPublicKeyInfo_payload_t
= { subjectPubKey_alg : algorithmIdentifier_t;
    subjectPubKey     : pubkey_t }

let parse_subjectPublicKeyInfo_payload_kind
: parser_kind
= parse_filter_kind
  (parse_asn1_envelop_tag_with_TLV_kind SEQUENCE
   `and_then_kind`
   parse_asn1_TLV_kind_of_type BIT_STRING)

val parse_subjectPublicKeyInfo_payload
: parser parse_subjectPublicKeyInfo_payload_kind (subjectPublicKeyInfo_payload_t)

val serialize_subjectPublicKeyInfo_payload
: serializer (parse_subjectPublicKeyInfo_payload)

val lemma_serialize_subjectPublicKeyInfo_payload_unfold
  (x: subjectPublicKeyInfo_payload_t)
: Lemma (
  serialize (serialize_subjectPublicKeyInfo_payload) x ==
  serialize (serialize_algorithmIdentifier) x.subjectPubKey_alg
  `Seq.append`
  serialize (serialize_asn1_TLV_of_type BIT_STRING) x.subjectPubKey
)

val lemma_serialize_subjectPublicKeyInfo_payload_size
  (x: subjectPublicKeyInfo_payload_t)
: Lemma (
  Seq.length (serialize (serialize_subjectPublicKeyInfo_payload) x) ==
  Seq.length (serialize (serialize_algorithmIdentifier) x.subjectPubKey_alg) +
  Seq.length (serialize (serialize_asn1_TLV_of_type BIT_STRING) x.subjectPubKey)
)

let subjectPublicKeyInfo_t
= inbound_sequence_value_of (serialize_subjectPublicKeyInfo_payload)

/// TLV
///
let parse_subjectPublicKeyInfo
: parser _ subjectPublicKeyInfo_t
= subjectPublicKeyInfo_t
  `coerce_parser`
  parse_asn1_sequence_TLV (serialize_subjectPublicKeyInfo_payload)

let serialize_subjectPublicKeyInfo
: serializer parse_subjectPublicKeyInfo
= coerce_parser_serializer
    parse_subjectPublicKeyInfo
    (serialize_asn1_sequence_TLV (serialize_subjectPublicKeyInfo_payload))
    ()

val lemma_serialize_subjectPublicKeyInfo_unfold
  (x: subjectPublicKeyInfo_t)
: Lemma ( predicate_serialize_asn1_sequence_TLV_unfold (serialize_subjectPublicKeyInfo_payload) x )

val lemma_serialize_subjectPublicKeyInfo_size
  (x: subjectPublicKeyInfo_t)
: Lemma ( predicate_serialize_asn1_sequence_TLV_size (serialize_subjectPublicKeyInfo_payload) x )

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

noextract inline_for_extraction unfold
[@@ "opaque_to_smt"]
let len_of_subjectPublicKeyInfo
: (len: asn1_TLV_int32_of_type SEQUENCE
        { v len == length_of_subjectPublicKeyInfo })
= 44ul

#push-options "--z3rlimit 32 --fuel 0 --ifuel 0"
val lemma_serialize_subjectPublicKeyInfo_size_exact
  (x: subjectPublicKeyInfo_t)
: Lemma (
  ( length_of_opaque_serialization (serialize_subjectPublicKeyInfo) x
    == length_of_subjectPublicKeyInfo )
)
#pop-options

/// Low
///

inline_for_extraction
val serialize32_subjectPublicKeyInfo_payload_backwards
: serializer32_backwards (serialize_subjectPublicKeyInfo_payload)

inline_for_extraction
val serialize32_subjectPublicKeyInfo_backwards
: serializer32_backwards (serialize_subjectPublicKeyInfo)

(* helpers *)

module B32 = FStar.Bytes
open X509.Crypto.AlgorithmIdentifier
let subjectPublicKeyInfo_raw_t
= B32.lbytes32 32ul

#push-options "--z3rlimit 16 --fuel 0 --ifuel 0"
let x509_get_subjectPublicKeyInfo
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
#pop-options
