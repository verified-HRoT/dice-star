module X509.BasicFields.SubjectPublicKeyInfo
open ASN1.Spec
open ASN1.Low

open X509.Base
open X509.Crypto

open FStar.Integers

(* SubjectPublicKeyInfo
  ======================
*)

let parse_subjectPublicKeyInfo_payload
= parse_algorithmIdentifier
  `nondep_then`
  parse_asn1_TLV_of_type BIT_STRING
  `parse_filter`
  filter_subjectPublicKeyInfo_payload_t'
  `parse_synth`
  synth_subjectPublicKeyInfo_payload_t

let serialize_subjectPublicKeyInfo_payload
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

let lemma_serialize_subjectPublicKeyInfo_payload_unfold x
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

let lemma_serialize_subjectPublicKeyInfo_payload_size x
= lemma_serialize_subjectPublicKeyInfo_payload_unfold x

let parse_subjectPublicKeyInfo
=
  subjectPublicKeyInfo_t
  `coerce_parser`
  parse_asn1_sequence_TLV (serialize_subjectPublicKeyInfo_payload)

let serialize_subjectPublicKeyInfo
= coerce_parser_serializer
    parse_subjectPublicKeyInfo
    (serialize_asn1_sequence_TLV (serialize_subjectPublicKeyInfo_payload))
    ()

let lemma_serialize_subjectPublicKeyInfo_unfold x
= lemma_serialize_asn1_sequence_TLV_unfold (serialize_subjectPublicKeyInfo_payload) x

let lemma_serialize_subjectPublicKeyInfo_size x
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

#push-options "--z3rlimit 32 --fuel 0 --ifuel 0"
let lemma_serialize_subjectPublicKeyInfo_size_exact x
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

let serialize32_subjectPublicKeyInfo_payload_backwards
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

let serialize32_subjectPublicKeyInfo_backwards
= coerce_serializer32_backwards
    (serialize_subjectPublicKeyInfo)
    (serialize32_asn1_sequence_TLV_backwards
     (* ls *) (serialize32_subjectPublicKeyInfo_payload_backwards))
    ()
(* helpers *)
