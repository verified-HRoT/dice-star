module L0.X509.AliasKeyTBS.Subject

open ASN1.Spec
open ASN1.Low
open X509
open FStar.Integers

open L0.X509.LengthUtils

module B32 = FStar.Bytes

#set-options "--z3rlimit 128 --fuel 0 --ifuel 0 --using_facts_from '* -FStar.Tactics -FStar.Reflection'"

noeq
type aliasKeyTBS_subject_payload_t = {
  aliasKeyTBS_subject_Common      : x509_RDN_x520_attribute_t COMMON_NAME  IA5_STRING;
  aliasKeyTBS_subject_Organization: x509_RDN_x520_attribute_t ORGANIZATION IA5_STRING;
  aliasKeyTBS_subject_Country     : x509_RDN_x520_attribute_t COUNTRY      PRINTABLE_STRING
}

noextract
let parse_aliasKeyTBS_subject_payload_kind
: parser_kind
= parse_asn1_envelop_tag_with_TLV_kind SET
  `and_then_kind`
  parse_asn1_envelop_tag_with_TLV_kind SET
  `and_then_kind`
  parse_asn1_envelop_tag_with_TLV_kind SET

noextract
val parse_aliasKeyTBS_subject_payload
: parser
    (parse_aliasKeyTBS_subject_payload_kind)
    (aliasKeyTBS_subject_payload_t)

noextract
val serialize_aliasKeyTBS_subject_payload
: serializer (parse_aliasKeyTBS_subject_payload)

// unfold
// [@@ "opaque_to_smt"]
let len_of_aliasKeyTBS_subject_payload_max ()
: GTot (asn1_value_int32_of_type SEQUENCE)
= len_of_RDN_x520_attribute_max COMMON_NAME  IA5_STRING +
  len_of_RDN_x520_attribute_max ORGANIZATION IA5_STRING +
  len_of_RDN_x520_attribute_max COUNTRY      PRINTABLE_STRING

// unfold
// [@@ "opaque_to_smt"]
let len_of_aliasKeyTBS_subject_payload
  (s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
: Tot (len: asn1_value_int32_of_type SEQUENCE
            { v len <= v (len_of_aliasKeyTBS_subject_payload_max ()) })
= len_of_RDN_x520_attribute s_common +
  len_of_RDN_x520_attribute s_org +
  len_of_RDN_x520_attribute s_country

val lemma_serialize_aliasKeyTBS_subject_payload_unfold
  (x: aliasKeyTBS_subject_payload_t)
: Lemma (
  serialize_aliasKeyTBS_subject_payload `serialize` x ==
 (serialize_RDN_x520_attribute COMMON_NAME  IA5_STRING `serialize` x.aliasKeyTBS_subject_Common)
  `Seq.append`
 (serialize_RDN_x520_attribute ORGANIZATION IA5_STRING `serialize` x.aliasKeyTBS_subject_Organization)
  `Seq.append`
 (serialize_RDN_x520_attribute COUNTRY PRINTABLE_STRING `serialize` x.aliasKeyTBS_subject_Country)
)

val lemma_serialize_aliasKeyTBS_subject_payload_size
  (x: aliasKeyTBS_subject_payload_t)
: Lemma (
  length_of_opaque_serialization (serialize_aliasKeyTBS_subject_payload) x
  == length_of_opaque_serialization (serialize_RDN_x520_attribute _ _) x.aliasKeyTBS_subject_Common +
     length_of_opaque_serialization (serialize_RDN_x520_attribute _ _) x.aliasKeyTBS_subject_Organization +
     length_of_opaque_serialization (serialize_RDN_x520_attribute _ _) x.aliasKeyTBS_subject_Country /\
  length_of_opaque_serialization (serialize_aliasKeyTBS_subject_payload) x
  == v (len_of_aliasKeyTBS_subject_payload
         (get_RDN_x520_attribute_string x.aliasKeyTBS_subject_Common)
         (get_RDN_x520_attribute_string x.aliasKeyTBS_subject_Organization)
         (get_RDN_x520_attribute_string x.aliasKeyTBS_subject_Country)) /\
  length_of_opaque_serialization (serialize_aliasKeyTBS_subject_payload) x
  <= v (len_of_aliasKeyTBS_subject_payload_max ())
)


(*
 *
 *)

let aliasKeyTBS_subject_t
= inbound_sequence_value_of (serialize_aliasKeyTBS_subject_payload)

noextract
let parse_aliasKeyTBS_subject
: parser (parse_asn1_envelop_tag_with_TLV_kind SEQUENCE) (aliasKeyTBS_subject_t)
= (aliasKeyTBS_subject_t)
  `coerce_parser`
  (parse_asn1_sequence_TLV
   (**) (serialize_aliasKeyTBS_subject_payload))

noextract
let serialize_aliasKeyTBS_subject
: serializer (parse_aliasKeyTBS_subject)
= coerce_parser_serializer
  (* p *) (parse_aliasKeyTBS_subject)
  (* s *) (serialize_asn1_sequence_TLV
          (**) (serialize_aliasKeyTBS_subject_payload))
  (*prf*) ()

noextract unfold
[@@ "opaque_to_smt"]
let len_of_aliasKeyTBS_subject_max ()
: GTot (asn1_TLV_int32_of_type SEQUENCE)
= SEQUENCE `len_of_TLV`
  (**) (len_of_aliasKeyTBS_subject_payload_max ())

// unfold
// [@@ "opaque_to_smt"]
let len_of_aliasKeyTBS_subject
  (s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
: Tot (len: asn1_TLV_int32_of_type SEQUENCE
            { v len <= v (len_of_aliasKeyTBS_subject_max ()) })
= SEQUENCE `len_of_TLV`
  (**) (len_of_aliasKeyTBS_subject_payload s_common s_org s_country)

val lemma_serialize_aliasKeyTBS_subject_unfold
  (x: aliasKeyTBS_subject_t)
: Lemma ( predicate_serialize_asn1_sequence_TLV_unfold (serialize_aliasKeyTBS_subject_payload) x )

val lemma_serialize_aliasKeyTBS_subject_size
  (x: aliasKeyTBS_subject_t)
: Lemma ( predicate_serialize_asn1_sequence_TLV_size (serialize_aliasKeyTBS_subject_payload) x )

val lemma_serialize_aliasKeyTBS_subject_size_exact
  (x: aliasKeyTBS_subject_t)
: Lemma (
  let _ = lemma_serialize_aliasKeyTBS_subject_payload_size x in
  length_of_opaque_serialization (serialize_aliasKeyTBS_subject) x
  == v (len_of_aliasKeyTBS_subject
         (get_RDN_x520_attribute_string x.aliasKeyTBS_subject_Common)
         (get_RDN_x520_attribute_string x.aliasKeyTBS_subject_Organization)
         (get_RDN_x520_attribute_string x.aliasKeyTBS_subject_Country)) /\
  length_of_opaque_serialization (serialize_aliasKeyTBS_subject) x
  <= v (len_of_aliasKeyTBS_subject_max ())
)

(* Low *)

//noextract inline_for_extraction
val serialize32_aliasKeyTBS_subject_payload_backwards
: serializer32_backwards (serialize_aliasKeyTBS_subject_payload)

//noextract inline_for_extraction
val serialize32_aliasKeyTBS_subject_backwards
: serializer32_backwards (serialize_aliasKeyTBS_subject)

(*
 *
 *)

let x509_get_aliasKeyTBS_subject
  (#len_common: asn1_value_int32_of_type IA5_STRING
                { x520_attribute_lb COMMON_NAME <= len_common /\
                  len_common <= x520_attribute_ub COMMON_NAME })
  (s32_common: character_string_lbytes32 IA5_STRING len_common)
  (#len_org: asn1_value_int32_of_type IA5_STRING
                { x520_attribute_lb ORGANIZATION <= len_org /\
                  len_org <= x520_attribute_ub ORGANIZATION })
  (s32_org: character_string_lbytes32 IA5_STRING len_org)
  (#len_country: asn1_value_int32_of_type PRINTABLE_STRING
                { x520_attribute_lb COUNTRY <= len_country /\
                  len_country <= x520_attribute_ub COUNTRY })
  (s32_country: character_string_lbytes32 PRINTABLE_STRING len_country)
: Tot (aliasKeyTBS_subject_t)
= let rdn_common: x509_RDN_x520_attribute_t COMMON_NAME IA5_STRING
    = x509_get_RDN_x520_attribute
          (asn1_get_character_string
            (len_common)
            (s32_common)) in
  let rdn_org: x509_RDN_x520_attribute_t ORGANIZATION IA5_STRING
    = x509_get_RDN_x520_attribute
          (asn1_get_character_string
            (len_org)
            (s32_org)) in
  let rdn_country: x509_RDN_x520_attribute_t COUNTRY PRINTABLE_STRING
    = x509_get_RDN_x520_attribute
          (asn1_get_character_string
            (len_country)
            (s32_country)) in
  let subject: aliasKeyTBS_subject_payload_t = {
    aliasKeyTBS_subject_Common       = rdn_common;
    aliasKeyTBS_subject_Organization = rdn_org;
    aliasKeyTBS_subject_Country      = rdn_country
  } in
  (* Prf *) lemma_serialize_aliasKeyTBS_subject_payload_unfold subject;
  (* Prf *) lemma_serialize_aliasKeyTBS_subject_payload_size   subject;
  (* Prf *) (**) lemma_serialize_RDN_x520_attribute_size_exact subject.aliasKeyTBS_subject_Common;
  (* Prf *) (**) lemma_serialize_RDN_x520_attribute_size_exact subject.aliasKeyTBS_subject_Organization;
  (* Prf *) (**) lemma_serialize_RDN_x520_attribute_size_exact subject.aliasKeyTBS_subject_Country;

(* return *) (subject)
