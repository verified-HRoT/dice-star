module RIoT.X509.AliasKeyTBS

open ASN1.Spec
open ASN1.Low
open X509
open RIoT.X509.AliasKeyTBS.Issuer
open RIoT.X509.AliasKeyTBS.Subject
open RIoT.X509.AliasKeyTBS.Extensions
open FStar.Integers

module B32 = FStar.Bytes

#set-options "--z3rlimit 256 --fuel 0 --ifuel 0 --using_facts_from '* -FStar.Tactics -FStar.Reflection'"

noeq
type aliasKeyTBS_payload_t = {
(*
 *       version         [0]  EXPLICIT Version DEFAULT v1,
 *)
  aliasKeyTBS_version     : x509_version_t;
(*
 *       serialNumber         CertificateSerialNumber,
 *)
  aliasKeyTBS_serialNumber: x509_serialNumber_t;
(*
 *       signature            AlgorithmIdentifier,
 *)
  aliasKeyTBS_signatureAlg: algorithmIdentifier_t;
(*
 *       issuer               Name,
 *)
  aliasKeyTBS_issuer      : aliasKeyTBS_issuer_t;
(*
 *       validity             Validity,
 *)
 aliasKeyTBS_validity     : x509_validity_t;
(*
 *       subject              Name,
 *)
  aliasKeyTBS_subject     : aliasKeyTBS_subject_t;
 (*
  *      subjectPublicKeyInfo SubjectPublicKeyInfo
  *)
  aliasKeyTBS_aliasKey_pub: subjectPublicKeyInfo_t;
 (*
  *      extensions      [3]  EXPLICIT Extensions OPTIONAL
  *)
  aliasKeyTBS_extensions  : x509_extensions_t_inbound
                              serialize_aliasKeyTBS_extensions
}

noextract
let parse_aliasKeyTBS_payload_kind
: parser_kind
= parse_x509_version_kind
  `and_then_kind`
  parse_filter_kind parse_big_integer_as_octet_string_TLV_kind
  `and_then_kind`
  parse_asn1_envelop_tag_with_TLV_kind SEQUENCE
  `and_then_kind`
  parse_asn1_envelop_tag_with_TLV_kind SEQUENCE
  `and_then_kind`
  parse_asn1_envelop_tag_with_TLV_kind SEQUENCE
  `and_then_kind`
  parse_asn1_envelop_tag_with_TLV_kind SEQUENCE
  `and_then_kind`
  parse_asn1_envelop_tag_with_TLV_kind SEQUENCE
  `and_then_kind`
  parse_asn1_envelop_tag_with_TLV_kind x509_extensions_outmost_explicit_tag

noextract
val parse_aliasKeyTBS_payload
: parser parse_aliasKeyTBS_payload_kind aliasKeyTBS_payload_t

noextract
val serialize_aliasKeyTBS_payload
: serializer (parse_aliasKeyTBS_payload)

val lemma_serialize_aliasKeyTBS_payload_unfold
  (x: aliasKeyTBS_payload_t)
: Lemma (
  serialize_aliasKeyTBS_payload `serialize` x ==
 (serialize_x509_version `serialize` x.aliasKeyTBS_version)
  `Seq.append`
 (serialize_x509_serialNumber `serialize` x.aliasKeyTBS_serialNumber)
  `Seq.append`
 (serialize_algorithmIdentifier `serialize` x.aliasKeyTBS_signatureAlg)
  `Seq.append`
 (serialize_aliasKeyTBS_issuer `serialize` x.aliasKeyTBS_issuer)
  `Seq.append`
 (serialize_x509_validity `serialize` x.aliasKeyTBS_validity)
  `Seq.append`
 (serialize_aliasKeyTBS_subject `serialize` x.aliasKeyTBS_subject)
  `Seq.append`
 (serialize_subjectPublicKeyInfo `serialize` x.aliasKeyTBS_aliasKey_pub)
  `Seq.append`
 (serialize_x509_extensions_TLV serialize_aliasKeyTBS_extensions `serialize` x.aliasKeyTBS_extensions)
)

let valid_aliasKeyTBS_ingredients
  (serialNumber: x509_serialNumber_t)
  (i_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (i_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (i_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (ku: key_usage_payload_t)
  (version: datatype_of_asn1_type INTEGER)
: Type0
= valid_aliasKeyTBS_extensions_ingredients ku version /\
  length_of_aliasKeyTBS_extensions ku version
  <= asn1_value_length_max_of_type x509_extensions_outmost_explicit_tag /\
  length_of_x509_version () +
  v (len_of_x509_serialNumber serialNumber) +
  v (len_of_algorithmIdentifier ()) +
  length_of_aliasKeyTBS_issuer i_common i_org i_country +
  length_of_x509_validity () +
  length_of_aliasKeyTBS_subject s_common s_org s_country +
  length_of_subjectPublicKeyInfo +
  length_of_x509_extensions (length_of_aliasKeyTBS_extensions ku version)
  <= asn1_value_length_max_of_type SEQUENCE

val lemma_aliasKeyTBS_ingredients_valid
  (serialNumber: x509_serialNumber_t)
  (i_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (i_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (i_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (ku: key_usage_payload_t)
  (version: datatype_of_asn1_type INTEGER)
: Lemma (
  valid_aliasKeyTBS_ingredients
    serialNumber
    i_common i_org i_country
    s_common s_org s_country
    ku version
)

let length_of_aliasKeyTBS_payload
  (serialNumber: x509_serialNumber_t)
  (i_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (i_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (i_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (ku: key_usage_payload_t)
  (version: datatype_of_asn1_type INTEGER)
: GTot (asn1_value_length_of_type SEQUENCE)
= lemma_aliasKeyTBS_extensions_ingredients_valid ku version;
  lemma_aliasKeyTBS_ingredients_valid
                serialNumber
                i_common i_org i_country
                s_common s_org s_country
                ku version;
  length_of_x509_version () +
  v (len_of_x509_serialNumber serialNumber) +
  v (len_of_algorithmIdentifier ()) +
  length_of_aliasKeyTBS_issuer i_common i_org i_country +
  length_of_x509_validity () +
  length_of_aliasKeyTBS_subject s_common s_org s_country +
  length_of_subjectPublicKeyInfo +
  length_of_x509_extensions (length_of_aliasKeyTBS_extensions ku version)

let len_of_aliasKeyTBS_payload
  (serialNumber: x509_serialNumber_t)
  (i_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (i_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (i_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (ku: key_usage_payload_t)
  (version: datatype_of_asn1_type INTEGER)
: Tot (len: asn1_TLV_int32_of_type SEQUENCE
            { v len == length_of_aliasKeyTBS_payload
                         serialNumber
                         i_common i_org i_country
                         s_common s_org s_country
                         ku version })
= lemma_aliasKeyTBS_extensions_ingredients_valid ku version;
  lemma_aliasKeyTBS_ingredients_valid
                serialNumber
                i_common i_org i_country
                s_common s_org s_country
                ku version;
  len_of_x509_version () +
  len_of_x509_serialNumber serialNumber +
  len_of_algorithmIdentifier () +
  len_of_aliasKeyTBS_issuer i_common i_org i_country +
  len_of_x509_validity () +
  len_of_aliasKeyTBS_subject s_common s_org s_country +
  len_of_subjectPublicKeyInfo +
  len_of_x509_extensions (len_of_aliasKeyTBS_extensions ku version)

unfold
let predicate_serialize_aliasKeyTBS_payload_size_unfold
  (x: aliasKeyTBS_payload_t)
: Type0
=
  length_of_opaque_serialization (serialize_aliasKeyTBS_payload) x ==
  length_of_opaque_serialization (serialize_x509_version)             x.aliasKeyTBS_version      +
  length_of_opaque_serialization (serialize_x509_serialNumber)        x.aliasKeyTBS_serialNumber +
  length_of_opaque_serialization (serialize_algorithmIdentifier)      x.aliasKeyTBS_signatureAlg +
  length_of_opaque_serialization (serialize_aliasKeyTBS_issuer)       x.aliasKeyTBS_issuer       +
  length_of_opaque_serialization (serialize_x509_validity)            x.aliasKeyTBS_validity     +
  length_of_opaque_serialization (serialize_aliasKeyTBS_subject)      x.aliasKeyTBS_subject      +
  length_of_opaque_serialization (serialize_subjectPublicKeyInfo)     x.aliasKeyTBS_aliasKey_pub +
  length_of_opaque_serialization (serialize_x509_extensions_TLV
                                  serialize_aliasKeyTBS_extensions)   x.aliasKeyTBS_extensions

val lemma_serialize_aliasKeyTBS_payload_size
  (x: aliasKeyTBS_payload_t)
: Lemma (
  let _ = lemma_aliasKeyTBS_ingredients_valid
            (x.aliasKeyTBS_serialNumber)
            (get_RDN_x520_attribute_string x.aliasKeyTBS_issuer.aliasKeyTBS_issuer_Common)
            (get_RDN_x520_attribute_string x.aliasKeyTBS_issuer.aliasKeyTBS_issuer_Organization)
            (get_RDN_x520_attribute_string x.aliasKeyTBS_issuer.aliasKeyTBS_issuer_Country)
            (get_RDN_x520_attribute_string x.aliasKeyTBS_subject.aliasKeyTBS_subject_Common)
            (get_RDN_x520_attribute_string x.aliasKeyTBS_subject.aliasKeyTBS_subject_Organization)
            (get_RDN_x520_attribute_string x.aliasKeyTBS_subject.aliasKeyTBS_subject_Country)
            (snd x.aliasKeyTBS_extensions.aliasKeyTBS_extensions_key_usage)
            RIoT.X509.Extension.(x.aliasKeyTBS_extensions.aliasKeyTBS_extensions_riot.x509_extValue_riot.riot_version) in
  lemma_serialize_aliasKeyTBS_payload_unfold x;
    lemma_serialize_x509_version_size_exact x.aliasKeyTBS_version;
    lemma_serialize_x509_serialNumber_size x.aliasKeyTBS_serialNumber;
    lemma_serialize_algorithmIdentifier_size_exact x.aliasKeyTBS_signatureAlg;
    lemma_serialize_aliasKeyTBS_issuer_size_exact x.aliasKeyTBS_issuer;
    lemma_serialize_x509_validity_size_exact x.aliasKeyTBS_validity;
    lemma_serialize_aliasKeyTBS_subject_size_exact x.aliasKeyTBS_subject;
    lemma_serialize_subjectPublicKeyInfo_size_exact x.aliasKeyTBS_aliasKey_pub;
    lemma_serialize_x509_extensions_TLV_size serialize_aliasKeyTBS_extensions x.aliasKeyTBS_extensions;
      lemma_serialize_aliasKeyTBS_extensions_size_exact x.aliasKeyTBS_extensions;
  predicate_serialize_aliasKeyTBS_payload_size_unfold x /\
  (* exact size *)
  length_of_opaque_serialization (serialize_aliasKeyTBS_payload) x
  == length_of_aliasKeyTBS_payload
       x.aliasKeyTBS_serialNumber
       (get_RDN_x520_attribute_string x.aliasKeyTBS_issuer.aliasKeyTBS_issuer_Common)
       (get_RDN_x520_attribute_string x.aliasKeyTBS_issuer.aliasKeyTBS_issuer_Organization)
       (get_RDN_x520_attribute_string x.aliasKeyTBS_issuer.aliasKeyTBS_issuer_Country)
       (get_RDN_x520_attribute_string x.aliasKeyTBS_subject.aliasKeyTBS_subject_Common)
       (get_RDN_x520_attribute_string x.aliasKeyTBS_subject.aliasKeyTBS_subject_Organization)
       (get_RDN_x520_attribute_string x.aliasKeyTBS_subject.aliasKeyTBS_subject_Country)
       (snd x.aliasKeyTBS_extensions.aliasKeyTBS_extensions_key_usage)
       RIoT.X509.Extension.(x.aliasKeyTBS_extensions.aliasKeyTBS_extensions_riot.x509_extValue_riot.riot_version)
)

let aliasKeyTBS_t
= inbound_sequence_value_of (serialize_aliasKeyTBS_payload)

noextract
let parse_aliasKeyTBS
: parser (parse_asn1_envelop_tag_with_TLV_kind SEQUENCE) (aliasKeyTBS_t)
=
  aliasKeyTBS_t
  `coerce_parser`
  parse_asn1_sequence_TLV (serialize_aliasKeyTBS_payload)

noextract
let serialize_aliasKeyTBS
: serializer (parse_aliasKeyTBS)
= coerce_parser_serializer
    (parse_aliasKeyTBS)
    (serialize_asn1_sequence_TLV (serialize_aliasKeyTBS_payload))
    ()

val lemma_serialize_aliasKeyTBS_unfold
  (x: aliasKeyTBS_t)
: Lemma ( predicate_serialize_asn1_sequence_TLV_unfold (serialize_aliasKeyTBS_payload) x )

val lemma_serialize_aliasKeyTBS_size
  (x: aliasKeyTBS_t)
: Lemma ( predicate_serialize_asn1_sequence_TLV_size (serialize_aliasKeyTBS_payload) x )

let length_of_aliasKeyTBS
  (serialNumber: x509_serialNumber_t)
  (i_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (i_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (i_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (ku: key_usage_payload_t)
  (version: datatype_of_asn1_type INTEGER)
: GTot (asn1_TLV_length_of_type SEQUENCE)
= lemma_aliasKeyTBS_ingredients_valid
    serialNumber
    i_common i_org i_country
    s_common s_org s_country
    ku version;
  length_of_TLV
    (SEQUENCE)
    (length_of_aliasKeyTBS_payload
      serialNumber
      i_common i_org i_country
      s_common s_org s_country
      ku version)

let len_of_aliasKeyTBS
  (serialNumber: x509_serialNumber_t)
  (i_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (i_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (i_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (ku: key_usage_payload_t)
  (version: datatype_of_asn1_type INTEGER)
: Tot (len: asn1_TLV_int32_of_type SEQUENCE
             { v len == length_of_aliasKeyTBS
                          serialNumber
                          i_common i_org i_country
                          s_common s_org s_country
                          ku version })
= lemma_aliasKeyTBS_ingredients_valid
    serialNumber
    i_common i_org i_country
    s_common s_org s_country
    ku version;
  len_of_TLV
    (SEQUENCE)
    (len_of_aliasKeyTBS_payload
      serialNumber
      i_common i_org i_country
      s_common s_org s_country
      ku version)

val lemma_serialize_aliasKeyTBS_size_exact
  (x: aliasKeyTBS_t)
: Lemma (
  lemma_aliasKeyTBS_ingredients_valid
          x.aliasKeyTBS_serialNumber
          (get_RDN_x520_attribute_string x.aliasKeyTBS_issuer.aliasKeyTBS_issuer_Common)
          (get_RDN_x520_attribute_string x.aliasKeyTBS_issuer.aliasKeyTBS_issuer_Organization)
          (get_RDN_x520_attribute_string x.aliasKeyTBS_issuer.aliasKeyTBS_issuer_Country)
          (get_RDN_x520_attribute_string x.aliasKeyTBS_subject.aliasKeyTBS_subject_Common)
          (get_RDN_x520_attribute_string x.aliasKeyTBS_subject.aliasKeyTBS_subject_Organization)
          (get_RDN_x520_attribute_string x.aliasKeyTBS_subject.aliasKeyTBS_subject_Country)
          (snd x.aliasKeyTBS_extensions.aliasKeyTBS_extensions_key_usage)
          RIoT.X509.Extension.(x.aliasKeyTBS_extensions.aliasKeyTBS_extensions_riot.x509_extValue_riot.riot_version);
  lemma_serialize_aliasKeyTBS_payload_size x;
  (* exact size *)
  length_of_opaque_serialization (serialize_aliasKeyTBS) x
  == length_of_aliasKeyTBS
       x.aliasKeyTBS_serialNumber
       (get_RDN_x520_attribute_string x.aliasKeyTBS_issuer.aliasKeyTBS_issuer_Common)
       (get_RDN_x520_attribute_string x.aliasKeyTBS_issuer.aliasKeyTBS_issuer_Organization)
       (get_RDN_x520_attribute_string x.aliasKeyTBS_issuer.aliasKeyTBS_issuer_Country)
       (get_RDN_x520_attribute_string x.aliasKeyTBS_subject.aliasKeyTBS_subject_Common)
       (get_RDN_x520_attribute_string x.aliasKeyTBS_subject.aliasKeyTBS_subject_Organization)
       (get_RDN_x520_attribute_string x.aliasKeyTBS_subject.aliasKeyTBS_subject_Country)
       (snd x.aliasKeyTBS_extensions.aliasKeyTBS_extensions_key_usage)
       RIoT.X509.Extension.(x.aliasKeyTBS_extensions.aliasKeyTBS_extensions_riot.x509_extValue_riot.riot_version)
)

(* low *)
val serialize32_aliasKeyTBS_payload_backwards
: serializer32_backwards (serialize_aliasKeyTBS_payload)

val serialize32_aliasKeyTBS_backwards
: serializer32_backwards (serialize_aliasKeyTBS)

(* helpers *)
let x509_get_AliasKeyTBS
  (crt_version: x509_version_t)
  (serialNumber: x509_serialNumber_t)
  (i_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (i_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (i_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (notBefore: datatype_of_asn1_type Generalized_Time)
  (notAfter : datatype_of_asn1_type Generalized_Time)
  (s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (ku: key_usage_payload_t)
  (keyID: datatype_of_asn1_type OCTET_STRING { dfst keyID == 20ul })
  (version: datatype_of_asn1_type INTEGER)
  (fwid: B32.lbytes32 32ul)
  (deviceIDPub: B32.lbytes32 32ul)
  (aliasKeyPub: B32.lbytes32 32ul)
: Tot (aliasKeyTBS_t)
= lemma_aliasKeyTBS_ingredients_valid
    serialNumber
    i_common i_org i_country
    s_common s_org s_country
    ku version;
  let signatureAlg: algorithmIdentifier_t = x509_get_algorithmIdentifier () in
  (* Prf *) lemma_serialize_algorithmIdentifier_size_exact signatureAlg;

  let issuer: aliasKeyTBS_issuer_t = x509_get_aliasKeyTBS_issuer
    #(dfst (i_common <: datatype_of_asn1_type IA5_STRING))
    (dsnd (i_common <: datatype_of_asn1_type IA5_STRING))
    #(dfst (i_org <: datatype_of_asn1_type IA5_STRING))
    (dsnd (i_org <: datatype_of_asn1_type IA5_STRING))
    #(dfst (i_country <: datatype_of_asn1_type PRINTABLE_STRING))
    (dsnd (i_country <: datatype_of_asn1_type PRINTABLE_STRING)) in
  (* Prf *) lemma_serialize_aliasKeyTBS_issuer_size_exact issuer;

  let validity: x509_validity_t = x509_get_validity
                                    notBefore
                                    notAfter in
  (* Prf *) lemma_serialize_x509_validity_size_exact validity;

  let subject: aliasKeyTBS_subject_t = x509_get_aliasKeyTBS_subject
    #(dfst (s_common <: datatype_of_asn1_type IA5_STRING))
    (dsnd (s_common <: datatype_of_asn1_type IA5_STRING))
    #(dfst (s_org <: datatype_of_asn1_type IA5_STRING))
    (dsnd (s_org <: datatype_of_asn1_type IA5_STRING))
    #(dfst (s_country <: datatype_of_asn1_type PRINTABLE_STRING))
    (dsnd (s_country <: datatype_of_asn1_type PRINTABLE_STRING)) in
  (* Prf *) lemma_serialize_aliasKeyTBS_subject_size_exact subject;

  let aliasKeyPubInfo = x509_get_subjectPublicKeyInfo
                           aliasKeyPub in
  (* Prf *) lemma_serialize_subjectPublicKeyInfo_size_exact aliasKeyPubInfo;

  let extensions = x509_get_aliasKeyTBS_extensions
                                 ku
                                 keyID
                                 version
                                 fwid
                                 deviceIDPub in
  (* Prf *) lemma_serialize_aliasKeyTBS_extensions_size_exact extensions;

  let aliasKeyTBS: aliasKeyTBS_payload_t = {
    aliasKeyTBS_version        = crt_version;
    aliasKeyTBS_serialNumber   = serialNumber;
    aliasKeyTBS_signatureAlg   = signatureAlg;
    aliasKeyTBS_issuer         = issuer;
    aliasKeyTBS_validity       = validity;
    aliasKeyTBS_subject        = subject;
    aliasKeyTBS_aliasKey_pub   = aliasKeyPubInfo;
    aliasKeyTBS_extensions     = extensions
  } in
  (* Prf *) lemma_serialize_aliasKeyTBS_payload_unfold aliasKeyTBS;
  (* Prf *) lemma_serialize_aliasKeyTBS_payload_size   aliasKeyTBS;
  (* Prf *) (**) lemma_serialize_x509_version_size_exact crt_version;
  (* Prf *) (**) lemma_serialize_x509_serialNumber_size serialNumber;

(*return*) aliasKeyTBS
