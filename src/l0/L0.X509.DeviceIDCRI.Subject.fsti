module L0.X509.DeviceIDCRI.Subject

open ASN1.Spec
open ASN1.Low
open X509
open FStar.Integers

open L0.X509.LengthUtils

module B32 = FStar.Bytes

#set-options "--z3rlimit 128 --fuel 0 --ifuel 0 --using_facts_from '* -FStar.Tactics -FStar.Reflection'"

val decl : unit

let x509_rdn_string_t = ASN1.Base.oid_t & ASN1.Base.character_string_t IA5_STRING

noeq
type deviceIDCRI_subject_payload_t = {
  deviceIDCRI_subject_Common      : x509_RDN_x520_attribute_t COMMON_NAME  IA5_STRING;
  deviceIDCRI_subject_Organization: x509_RDN_x520_attribute_t ORGANIZATION IA5_STRING;
  deviceIDCRI_subject_Country     : x509_RDN_x520_attribute_t COUNTRY      PRINTABLE_STRING
}

inline_for_extraction noextract
let parse_deviceIDCRI_subject_payload_kind
: parser_kind
= parse_asn1_envelop_tag_with_TLV_kind SET
  `and_then_kind`
  parse_asn1_envelop_tag_with_TLV_kind SET
  `and_then_kind`
  parse_asn1_envelop_tag_with_TLV_kind SET

noextract
val parse_deviceIDCRI_subject_payload
: parser
    (parse_deviceIDCRI_subject_payload_kind)
    (deviceIDCRI_subject_payload_t)

noextract
val serialize_deviceIDCRI_subject_payload
: serializer (parse_deviceIDCRI_subject_payload)

// unfold
// [@@ "opaque_to_smt"]
let len_of_deviceIDCRI_subject_payload_max ()
: GTot (asn1_value_int32_of_type SEQUENCE)
= len_of_RDN_x520_attribute_max COMMON_NAME  IA5_STRING +
  len_of_RDN_x520_attribute_max ORGANIZATION IA5_STRING +
  len_of_RDN_x520_attribute_max COUNTRY      PRINTABLE_STRING

// unfold
// [@@ "opaque_to_smt"]
let len_of_deviceIDCRI_subject_payload
  (s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
: Tot (len: asn1_value_int32_of_type SEQUENCE
            { v len <= v (len_of_deviceIDCRI_subject_payload_max ()) })
= len_of_RDN_x520_attribute s_common +
  len_of_RDN_x520_attribute s_org +
  len_of_RDN_x520_attribute s_country

val lemma_serialize_deviceIDCRI_subject_payload_unfold
  (x: deviceIDCRI_subject_payload_t)
: Lemma (
  serialize_deviceIDCRI_subject_payload `serialize` x ==
 (serialize_RDN_x520_attribute COMMON_NAME  IA5_STRING `serialize` x.deviceIDCRI_subject_Common)
  `Seq.append`
 (serialize_RDN_x520_attribute ORGANIZATION IA5_STRING `serialize` x.deviceIDCRI_subject_Organization)
  `Seq.append`
 (serialize_RDN_x520_attribute COUNTRY PRINTABLE_STRING `serialize` x.deviceIDCRI_subject_Country)
)

val lemma_serialize_deviceIDCRI_subject_payload_size
  (x: deviceIDCRI_subject_payload_t)
: Lemma (
  length_of_opaque_serialization (serialize_deviceIDCRI_subject_payload) x
  == length_of_opaque_serialization (serialize_RDN_x520_attribute _ _) x.deviceIDCRI_subject_Common +
     length_of_opaque_serialization (serialize_RDN_x520_attribute _ _) x.deviceIDCRI_subject_Organization +
     length_of_opaque_serialization (serialize_RDN_x520_attribute _ _) x.deviceIDCRI_subject_Country /\
  length_of_opaque_serialization (serialize_deviceIDCRI_subject_payload) x
  == v (len_of_deviceIDCRI_subject_payload
         (get_RDN_x520_attribute_string x.deviceIDCRI_subject_Common)
         (get_RDN_x520_attribute_string x.deviceIDCRI_subject_Organization)
         (get_RDN_x520_attribute_string x.deviceIDCRI_subject_Country)) /\
  length_of_opaque_serialization (serialize_deviceIDCRI_subject_payload) x
  <= v (len_of_deviceIDCRI_subject_payload_max ())
)


(*
 *
 *)

let deviceIDCRI_subject_t
= inbound_sequence_value_of (serialize_deviceIDCRI_subject_payload)

noextract
let parse_deviceIDCRI_subject
: parser (parse_asn1_envelop_tag_with_TLV_kind SEQUENCE) (deviceIDCRI_subject_t)
= (deviceIDCRI_subject_t)
  `coerce_parser`
  (parse_asn1_sequence_TLV
   (**) (serialize_deviceIDCRI_subject_payload))

noextract
let serialize_deviceIDCRI_subject
: serializer (parse_deviceIDCRI_subject)
= coerce_parser_serializer
  (* p *) (parse_deviceIDCRI_subject)
  (* s *) (serialize_asn1_sequence_TLV
          (**) (serialize_deviceIDCRI_subject_payload))
  (*prf*) ()

noextract unfold
[@@ "opaque_to_smt"]
let len_of_deviceIDCRI_subject_max ()
: GTot (asn1_TLV_int32_of_type SEQUENCE)
= SEQUENCE `len_of_TLV`
  (**) (len_of_deviceIDCRI_subject_payload_max ())

// unfold
// [@@ "opaque_to_smt"]
let len_of_deviceIDCRI_subject
  (s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
: Tot (len: asn1_TLV_int32_of_type SEQUENCE
            { v len <= v (len_of_deviceIDCRI_subject_max ()) })
= SEQUENCE `len_of_TLV`
  (**) (len_of_deviceIDCRI_subject_payload s_common s_org s_country)

val lemma_serialize_deviceIDCRI_subject_unfold
  (x: deviceIDCRI_subject_t)
: Lemma ( predicate_serialize_asn1_sequence_TLV_unfold (serialize_deviceIDCRI_subject_payload) x )

val lemma_serialize_deviceIDCRI_subject_size
  (x: deviceIDCRI_subject_t)
: Lemma ( predicate_serialize_asn1_sequence_TLV_size (serialize_deviceIDCRI_subject_payload) x )

val lemma_serialize_deviceIDCRI_subject_size_exact
  (x: deviceIDCRI_subject_t)
: Lemma (
  let _ = lemma_serialize_deviceIDCRI_subject_payload_size x in
  length_of_opaque_serialization (serialize_deviceIDCRI_subject) x
  == v (len_of_deviceIDCRI_subject
         (get_RDN_x520_attribute_string x.deviceIDCRI_subject_Common)
         (get_RDN_x520_attribute_string x.deviceIDCRI_subject_Organization)
         (get_RDN_x520_attribute_string x.deviceIDCRI_subject_Country)) /\
  length_of_opaque_serialization (serialize_deviceIDCRI_subject) x
  <= v (len_of_deviceIDCRI_subject_max ())
)

(* Low *)

//noextract inline_for_extraction
val serialize32_deviceIDCRI_subject_payload_backwards
: serializer32_backwards (serialize_deviceIDCRI_subject_payload)

//noextract inline_for_extraction
val serialize32_deviceIDCRI_subject_backwards
: serializer32_backwards (serialize_deviceIDCRI_subject)

(*
 *
 *)

let x509_get_deviceIDCRI_subject
  (s_common:character_string_t IA5_STRING{
    x520_attribute_lb COMMON_NAME <= dfst s_common /\
    dfst s_common <= x520_attribute_ub COMMON_NAME})
  (s_org:character_string_t IA5_STRING{
    x520_attribute_lb ORGANIZATION <= dfst s_org /\
    dfst s_org <= x520_attribute_ub ORGANIZATION})
  (s_country:character_string_t PRINTABLE_STRING{
    x520_attribute_lb COUNTRY <= dfst s_country /\
    dfst s_country <= x520_attribute_ub COUNTRY})
: Tot (deviceIDCRI_subject_t)
= let rdn_common: x509_RDN_x520_attribute_t COMMON_NAME IA5_STRING
    = x509_get_RDN_x520_attribute s_common in
  let rdn_org: x509_RDN_x520_attribute_t ORGANIZATION IA5_STRING
    = x509_get_RDN_x520_attribute s_org in
  let rdn_country: x509_RDN_x520_attribute_t COUNTRY PRINTABLE_STRING
    = x509_get_RDN_x520_attribute s_country in
  let subject: deviceIDCRI_subject_payload_t = {
    deviceIDCRI_subject_Common       = rdn_common;
    deviceIDCRI_subject_Organization = rdn_org;
    deviceIDCRI_subject_Country      = rdn_country
  } in
  (* Prf *) lemma_serialize_deviceIDCRI_subject_payload_unfold subject;
  (* Prf *) lemma_serialize_deviceIDCRI_subject_payload_size   subject;
  (* Prf *) (**) lemma_serialize_RDN_x520_attribute_size_exact subject.deviceIDCRI_subject_Common;
  (* Prf *) (**) lemma_serialize_RDN_x520_attribute_size_exact subject.deviceIDCRI_subject_Organization;
  (* Prf *) (**) lemma_serialize_RDN_x520_attribute_size_exact subject.deviceIDCRI_subject_Country;

(* return *) (subject)
