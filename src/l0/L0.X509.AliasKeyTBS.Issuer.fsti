module L0.X509.AliasKeyTBS.Issuer

open ASN1.Spec
open ASN1.Low
open X509
open FStar.Integers

open L0.X509.LengthUtils

module B32 = FStar.Bytes

#set-options "--z3rlimit 128 --fuel 0 --ifuel 0 --using_facts_from '* -FStar.Tactics -FStar.Reflection'"

val decl : unit

noeq
type aliasKeyTBS_issuer_payload_t = {
  aliasKeyTBS_issuer_Common      : x509_RDN_x520_attribute_t COMMON_NAME  IA5_STRING;
  aliasKeyTBS_issuer_Organization: x509_RDN_x520_attribute_t ORGANIZATION IA5_STRING;
  aliasKeyTBS_issuer_Country     : x509_RDN_x520_attribute_t COUNTRY      PRINTABLE_STRING
}

noextract
let parse_aliasKeyTBS_issuer_payload_kind
: parser_kind
= parse_asn1_envelop_tag_with_TLV_kind SET
  `and_then_kind`
  parse_asn1_envelop_tag_with_TLV_kind SET
  `and_then_kind`
  parse_asn1_envelop_tag_with_TLV_kind SET

noextract
val parse_aliasKeyTBS_issuer_payload
: parser
    (parse_aliasKeyTBS_issuer_payload_kind)
    (aliasKeyTBS_issuer_payload_t)

noextract
val serialize_aliasKeyTBS_issuer_payload
: serializer (parse_aliasKeyTBS_issuer_payload)

// unfold
// [@@ "opaque_to_smt"]
let len_of_aliasKeyTBS_issuer_payload_max ()
: GTot (asn1_value_int32_of_type SEQUENCE)
= len_of_RDN_x520_attribute_max COMMON_NAME  IA5_STRING +
  len_of_RDN_x520_attribute_max ORGANIZATION IA5_STRING +
  len_of_RDN_x520_attribute_max COUNTRY      PRINTABLE_STRING

// unfold
// [@@ "opaque_to_smt"]
let len_of_aliasKeyTBS_issuer_payload
  (s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
: Tot (len: asn1_value_int32_of_type SEQUENCE
            { v len <= v (len_of_aliasKeyTBS_issuer_payload_max ()) })
= len_of_RDN_x520_attribute s_common +
  len_of_RDN_x520_attribute s_org +
  len_of_RDN_x520_attribute s_country

val lemma_serialize_aliasKeyTBS_issuer_payload_unfold
  (x: aliasKeyTBS_issuer_payload_t)
: Lemma (
  serialize_aliasKeyTBS_issuer_payload `serialize` x ==
 (serialize_RDN_x520_attribute COMMON_NAME  IA5_STRING `serialize` x.aliasKeyTBS_issuer_Common)
  `Seq.append`
 (serialize_RDN_x520_attribute ORGANIZATION IA5_STRING `serialize` x.aliasKeyTBS_issuer_Organization)
  `Seq.append`
 (serialize_RDN_x520_attribute COUNTRY PRINTABLE_STRING `serialize` x.aliasKeyTBS_issuer_Country)
)

val lemma_serialize_aliasKeyTBS_issuer_payload_size
  (x: aliasKeyTBS_issuer_payload_t)
: Lemma (
  length_of_opaque_serialization (serialize_aliasKeyTBS_issuer_payload) x
  == length_of_opaque_serialization (serialize_RDN_x520_attribute _ _) x.aliasKeyTBS_issuer_Common +
     length_of_opaque_serialization (serialize_RDN_x520_attribute _ _) x.aliasKeyTBS_issuer_Organization +
     length_of_opaque_serialization (serialize_RDN_x520_attribute _ _) x.aliasKeyTBS_issuer_Country /\
  length_of_opaque_serialization (serialize_aliasKeyTBS_issuer_payload) x
  == v (len_of_aliasKeyTBS_issuer_payload
         (get_RDN_x520_attribute_string x.aliasKeyTBS_issuer_Common)
         (get_RDN_x520_attribute_string x.aliasKeyTBS_issuer_Organization)
         (get_RDN_x520_attribute_string x.aliasKeyTBS_issuer_Country)) /\
  length_of_opaque_serialization (serialize_aliasKeyTBS_issuer_payload) x
  <= v (len_of_aliasKeyTBS_issuer_payload_max ())
)


(*
 *
 *)

let aliasKeyTBS_issuer_t
= inbound_sequence_value_of (serialize_aliasKeyTBS_issuer_payload)

noextract
let parse_aliasKeyTBS_issuer
: parser (parse_asn1_envelop_tag_with_TLV_kind SEQUENCE) (aliasKeyTBS_issuer_t)
= (aliasKeyTBS_issuer_t)
  `coerce_parser`
  (parse_asn1_sequence_TLV
   (**) (serialize_aliasKeyTBS_issuer_payload))

noextract
let serialize_aliasKeyTBS_issuer
: serializer (parse_aliasKeyTBS_issuer)
= coerce_parser_serializer
  (* p *) (parse_aliasKeyTBS_issuer)
  (* s *) (serialize_asn1_sequence_TLV
          (**) (serialize_aliasKeyTBS_issuer_payload))
  (*prf*) ()

noextract unfold
[@@ "opaque_to_smt"]
let len_of_aliasKeyTBS_issuer_max ()
: GTot (asn1_TLV_int32_of_type SEQUENCE)
= SEQUENCE `len_of_TLV`
  (**) (len_of_aliasKeyTBS_issuer_payload_max ())

// unfold
// [@@ "opaque_to_smt"]
let len_of_aliasKeyTBS_issuer
  (s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
: Tot (len: asn1_TLV_int32_of_type SEQUENCE
            { v len <= v (len_of_aliasKeyTBS_issuer_max ()) })
= SEQUENCE `len_of_TLV`
  (**) (len_of_aliasKeyTBS_issuer_payload s_common s_org s_country)

val lemma_serialize_aliasKeyTBS_issuer_unfold
  (x: aliasKeyTBS_issuer_t)
: Lemma ( predicate_serialize_asn1_sequence_TLV_unfold (serialize_aliasKeyTBS_issuer_payload) x )

val lemma_serialize_aliasKeyTBS_issuer_size
  (x: aliasKeyTBS_issuer_t)
: Lemma ( predicate_serialize_asn1_sequence_TLV_size (serialize_aliasKeyTBS_issuer_payload) x )

val lemma_serialize_aliasKeyTBS_issuer_size_exact
  (x: aliasKeyTBS_issuer_t)
: Lemma (
  let _ = lemma_serialize_aliasKeyTBS_issuer_payload_size x in
  length_of_opaque_serialization (serialize_aliasKeyTBS_issuer) x
  == v (len_of_aliasKeyTBS_issuer
         (get_RDN_x520_attribute_string x.aliasKeyTBS_issuer_Common)
         (get_RDN_x520_attribute_string x.aliasKeyTBS_issuer_Organization)
         (get_RDN_x520_attribute_string x.aliasKeyTBS_issuer_Country)) /\
  length_of_opaque_serialization (serialize_aliasKeyTBS_issuer) x
  <= v (len_of_aliasKeyTBS_issuer_max ())
)

(* Low *)

//noextract inline_for_extraction
val serialize32_aliasKeyTBS_issuer_payload_backwards
: serializer32_backwards (serialize_aliasKeyTBS_issuer_payload)

//noextract inline_for_extraction
val serialize32_aliasKeyTBS_issuer_backwards
: serializer32_backwards (serialize_aliasKeyTBS_issuer)

(*
 *
 *)

let x509_get_aliasKeyTBS_issuer
  (s_common:character_string_t IA5_STRING{
    x520_attribute_lb COMMON_NAME <= dfst s_common /\
    dfst s_common <= x520_attribute_ub COMMON_NAME})
  (s_org:character_string_t IA5_STRING{
    x520_attribute_lb ORGANIZATION <= dfst s_org /\
    dfst s_org <= x520_attribute_ub ORGANIZATION})
  (s_country:character_string_t PRINTABLE_STRING{
    x520_attribute_lb COUNTRY <= dfst s_country /\
    dfst s_country <= x520_attribute_ub COUNTRY})
: Tot (aliasKeyTBS_issuer_t)
= let rdn_common: x509_RDN_x520_attribute_t COMMON_NAME IA5_STRING
    = x509_get_RDN_x520_attribute s_common in
  let rdn_org: x509_RDN_x520_attribute_t ORGANIZATION IA5_STRING
    = x509_get_RDN_x520_attribute s_org in
  let rdn_country: x509_RDN_x520_attribute_t COUNTRY PRINTABLE_STRING
    = x509_get_RDN_x520_attribute s_country in
  let issuer: aliasKeyTBS_issuer_payload_t = {
    aliasKeyTBS_issuer_Common       = rdn_common;
    aliasKeyTBS_issuer_Organization = rdn_org;
    aliasKeyTBS_issuer_Country      = rdn_country
  } in
  (* Prf *) lemma_serialize_aliasKeyTBS_issuer_payload_unfold issuer;
  (* Prf *) lemma_serialize_aliasKeyTBS_issuer_payload_size   issuer;
  (* Prf *) (**) lemma_serialize_RDN_x520_attribute_size_exact issuer.aliasKeyTBS_issuer_Common;
  (* Prf *) (**) lemma_serialize_RDN_x520_attribute_size_exact issuer.aliasKeyTBS_issuer_Organization;
  (* Prf *) (**) lemma_serialize_RDN_x520_attribute_size_exact issuer.aliasKeyTBS_issuer_Country;

(* return *) (issuer)
