module RIoT.X509.AliasKeyTBS

open ASN1.Spec
open ASN1.Low
open X509
open RIoT.X509.AliasKeyTBS.Issuer
open RIoT.X509.AliasKeyTBS.Subject
open RIoT.X509.AliasKeyTBS.Extensions
open FStar.Integers

open RIoT.X509.LengthUtils

module B32 = FStar.Bytes

#set-options "--z3rlimit 256 --fuel 0 --ifuel 0 --using_facts_from '* -FStar.Tactics -FStar.Reflection -LowParse'"

#set-options "--__temp_no_proj RIoT.X509.AliasKeyTBS"

val decl : unit

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
let and_then_kind (k1 k2:parser_kind) = and_then_kind k1 k2

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

#push-options "--z3rlimit 32"
let len_of_aliasKeyTBS_payload_max ()
: GTot (asn1_value_int32_of_type SEQUENCE)
= len_of_x509_version () +
  len_of_x509_serialNumber_max +
  len_of_algorithmIdentifier () +
  len_of_aliasKeyTBS_issuer_max () +
  len_of_x509_validity () +
  len_of_aliasKeyTBS_subject_max () +
  len_of_subjectPublicKeyInfo +
  len_of_x509_extensions (len_of_aliasKeyTBS_extensions_max ())

let len_of_aliasKeyTBS_payload
  (serialNumber: x509_serialNumber_t)
  (i_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (i_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (i_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (version: datatype_of_asn1_type INTEGER)
: Tot (len: asn1_value_int32_of_type SEQUENCE
            { v len <= v (len_of_aliasKeyTBS_payload_max ()) })
= len_of_x509_version () +
  len_of_x509_serialNumber serialNumber +
  len_of_algorithmIdentifier () +
  len_of_aliasKeyTBS_issuer i_common i_org i_country +
  len_of_x509_validity () +
  len_of_aliasKeyTBS_subject s_common s_org s_country +
  len_of_subjectPublicKeyInfo +
  len_of_x509_extensions (len_of_aliasKeyTBS_extensions version)
#pop-options

unfold
let predicate_serialize_aliasKeyTBS_payload_size_unfold
  (x: aliasKeyTBS_payload_t)
: Type0
=
  length_of_opaque_serialization (serialize_aliasKeyTBS_payload)      x ==
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
  predicate_serialize_aliasKeyTBS_payload_size_unfold x /\
  (* exact size *)
  length_of_opaque_serialization (serialize_aliasKeyTBS_payload) x
  == v (len_of_aliasKeyTBS_payload
          x.aliasKeyTBS_serialNumber
          (get_RDN_x520_attribute_string x.aliasKeyTBS_issuer.aliasKeyTBS_issuer_Common)
          (get_RDN_x520_attribute_string x.aliasKeyTBS_issuer.aliasKeyTBS_issuer_Organization)
          (get_RDN_x520_attribute_string x.aliasKeyTBS_issuer.aliasKeyTBS_issuer_Country)
          (get_RDN_x520_attribute_string x.aliasKeyTBS_subject.aliasKeyTBS_subject_Common)
          (get_RDN_x520_attribute_string x.aliasKeyTBS_subject.aliasKeyTBS_subject_Organization)
          (get_RDN_x520_attribute_string x.aliasKeyTBS_subject.aliasKeyTBS_subject_Country)
          RIoT.X509.Extension.(x.aliasKeyTBS_extensions.aliasKeyTBS_extensions_riot.x509_extValue_riot.riot_version))
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

[@@ "opaque_to_smt"]
unfold
let len_of_aliasKeyTBS_max ()
= SEQUENCE `len_of_TLV`
  (**) (len_of_aliasKeyTBS_payload_max ())

let len_of_aliasKeyTBS
  (serialNumber: x509_serialNumber_t)
  (i_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (i_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (i_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (version: datatype_of_asn1_type INTEGER)
: Tot (asn1_TLV_int32_of_type SEQUENCE)
= len_of_TLV
    (SEQUENCE)
    (len_of_aliasKeyTBS_payload
      serialNumber
      i_common i_org i_country
      s_common s_org s_country
      version)

val lemma_serialize_aliasKeyTBS_size_exact
  (x: aliasKeyTBS_t)
: Lemma (
  (* exact size *)
  length_of_opaque_serialization (serialize_aliasKeyTBS) x
  == v (len_of_aliasKeyTBS
         x.aliasKeyTBS_serialNumber
         (get_RDN_x520_attribute_string x.aliasKeyTBS_issuer.aliasKeyTBS_issuer_Common)
         (get_RDN_x520_attribute_string x.aliasKeyTBS_issuer.aliasKeyTBS_issuer_Organization)
         (get_RDN_x520_attribute_string x.aliasKeyTBS_issuer.aliasKeyTBS_issuer_Country)
         (get_RDN_x520_attribute_string x.aliasKeyTBS_subject.aliasKeyTBS_subject_Common)
         (get_RDN_x520_attribute_string x.aliasKeyTBS_subject.aliasKeyTBS_subject_Organization)
         (get_RDN_x520_attribute_string x.aliasKeyTBS_subject.aliasKeyTBS_subject_Country)
         RIoT.X509.Extension.(x.aliasKeyTBS_extensions.aliasKeyTBS_extensions_riot.x509_extValue_riot.riot_version))
)

(* low *)
val serialize32_aliasKeyTBS_payload_backwards
: serializer32_backwards (serialize_aliasKeyTBS_payload)

val serialize32_aliasKeyTBS_backwards
: serializer32_backwards (serialize_aliasKeyTBS)

(* helpers *)

#push-options "--z3rlimit 128"
open RIoT.X509.LengthUtils
let x509_get_AliasKeyTBS
  (crt_version: x509_version_t)
  (serialNumber: x509_serialNumber_t)
  (i_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (i_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (i_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (notBefore: datatype_of_asn1_type UTC_TIME)
  (notAfter : datatype_of_asn1_type Generalized_Time)
  (s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (ku: key_usage_payload_t)
  (keyID: datatype_of_asn1_type OCTET_STRING { keyID.ASN1.Base.len == 20ul })
  (version: datatype_of_asn1_type INTEGER)
  (fwid: B32.lbytes32 32ul)
  (deviceIDPub: B32.lbytes32 32ul)
  (aliasKeyPub: B32.lbytes32 32ul)
: Tot (aliasKeyTBS_t)
= let signatureAlg: algorithmIdentifier_t = x509_get_algorithmIdentifier () in
  (* Prf *) lemma_serialize_algorithmIdentifier_size_exact signatureAlg;

  [@inline_let]
  let i_common = coerce_x509_rdn_attribute_t_string_to_asn1_string_cn i_common in
  [@inline_let]
  let i_org = coerce_x509_rdn_attribute_t_string_to_asn1_string_org i_org in
  [@inline_let]
  let i_country = coerce_x509_rdn_attribute_t_string_to_asn1_string_country i_country in

  let issuer: aliasKeyTBS_issuer_t = x509_get_aliasKeyTBS_issuer
    #(dfst i_common)
    (dsnd i_common)
    #(dfst i_org)
    (dsnd i_org)
    #(dfst i_country)
    (dsnd i_country) in

  (* Prf *) lemma_serialize_aliasKeyTBS_issuer_size_exact issuer;

  let validity: x509_validity_t = x509_get_validity
                                    notBefore
                                    notAfter in
  (* Prf *) lemma_serialize_x509_validity_size_exact validity;

  [@inline_let]
  let s_common = coerce_x509_rdn_attribute_t_string_to_asn1_string_cn s_common in
  [@inline_let]
  let s_org = coerce_x509_rdn_attribute_t_string_to_asn1_string_org s_org in
  [@inline_let]
  let s_country = coerce_x509_rdn_attribute_t_string_to_asn1_string_country s_country in

  let subject: aliasKeyTBS_subject_t = x509_get_aliasKeyTBS_subject
    #(dfst s_common)
    (dsnd s_common)
    #(dfst s_org)
    (dsnd s_org)
    #(dfst s_country)
    (dsnd s_country) in
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
#pop-options
