module RIoT.X509.DeviceIDCRI

open ASN1.Spec
open ASN1.Low
open X509
open RIoT.X509.DeviceIDCRI.Subject
open RIoT.X509.DeviceIDCRI.Attributes
open FStar.Integers

module B32 = FStar.Bytes

#set-options "--z3rlimit 128 --fuel 0 --ifuel 0 --using_facts_from '* -FStar.Tactics -FStar.Reflection'"

(*     (To-Be-Signed) DeviceID Certification Request Info
 *================================================================
 *   CertificationRequestInfo ::= SEQUENCE {
 *        version       INTEGER { v1(0) } (v1,...),
 *        subject       Name,
 *        subjectPKInfo SubjectPublicKeyInfo{{ PKInfoAlgorithms }},
 *        attributes    [0] Attributes{{ CRIAttributes }}
 *   }
 *
 *)

noeq
type deviceIDCRI_payload_t = {
  deviceIDCRI_version: datatype_of_asn1_type INTEGER;
  deviceIDCRI_subject: deviceIDCRI_subject_t;
  deviceIDCRI_subjectPKInfo: subjectPublicKeyInfo_t;
  deviceIDCRI_attributes: deviceIDCRI_attributes_t
}

noextract
let parse_deviceIDCRI_payload_kind
: parser_kind
= parse_asn1_TLV_kind_of_type INTEGER
  `and_then_kind`
  parse_asn1_envelop_tag_with_TLV_kind SEQUENCE
  `and_then_kind`
  parse_asn1_envelop_tag_with_TLV_kind SEQUENCE
  `and_then_kind`
  parse_asn1_envelop_tag_with_TLV_kind
    (CUSTOM_TAG CONTEXT_SPECIFIC CONSTRUCTED 0uy `asn1_implicit_tagging` SET)

(*
 * Specification
 *)
val parse_deviceIDCRI_payload
: parser parse_deviceIDCRI_payload_kind (deviceIDCRI_payload_t)

val serialize_deviceIDCRI_payload
: serializer (parse_deviceIDCRI_payload)

val lemma_serialize_deviceIDCRI_payload_unfold
  (x: deviceIDCRI_payload_t)
: Lemma (
  serialize_deviceIDCRI_payload `serialize` x ==
 (serialize_asn1_TLV_of_type INTEGER `serialize` x.deviceIDCRI_version)
  `Seq.append`
 (serialize_deviceIDCRI_subject `serialize` x.deviceIDCRI_subject)
  `Seq.append`
 (serialize_subjectPublicKeyInfo `serialize` x.deviceIDCRI_subjectPKInfo)
  `Seq.append`
 (serialize_deviceIDCRI_attributes `serialize` x.deviceIDCRI_attributes)
)

[@@ "opaque_to_smt"]
unfold
let len_of_deviceIDCRI_payload_max ()
: Tot (asn1_value_int32_of_type SEQUENCE)
// = len_of_asn1_primitive_TLV #INTEGER version +
= asn1_TLV_int32_max_of_type INTEGER +
  len_of_deviceIDCRI_subject_max () +
  len_of_subjectPublicKeyInfo +
  len_of_deviceIDCRI_attributes ()

let len_of_deviceIDCRI_payload
  (version: datatype_of_asn1_type INTEGER)
  (s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
: Tot (asn1_value_int32_of_type SEQUENCE)
= len_of_asn1_primitive_TLV #INTEGER version +
  len_of_deviceIDCRI_subject s_common s_org s_country +
  len_of_subjectPublicKeyInfo +
  len_of_deviceIDCRI_attributes ()

val lemma_serialize_deviceIDCRI_payload_size
  (x: deviceIDCRI_payload_t)
: Lemma (
  let attrs' = coerce_envelop
                (CUSTOM_TAG CONTEXT_SPECIFIC CONSTRUCTED 0uy `asn1_implicit_tagging` SET)
                (SEQUENCE)
                (OID_PKCS9_CSR_EXT_REQ `serialize_envelop_OID_with`
                (**) (SET `serialize_asn1_envelop_tag_with_TLV`
                     (**) (SEQUENCE `serialize_asn1_envelop_tag_with_TLV`
                          (**) serialize_deviceIDCRI_attributes_extensionRequest_payload)))
                (x.deviceIDCRI_attributes) in
  length_of_opaque_serialization (serialize_deviceIDCRI_payload)      x ==
  length_of_opaque_serialization (serialize_asn1_TLV_of_type INTEGER) x.deviceIDCRI_version +
  length_of_opaque_serialization (serialize_deviceIDCRI_subject)      x.deviceIDCRI_subject +
  length_of_opaque_serialization (serialize_subjectPublicKeyInfo)     x.deviceIDCRI_subjectPKInfo +
  length_of_opaque_serialization (serialize_deviceIDCRI_attributes)   x.deviceIDCRI_attributes /\
  length_of_opaque_serialization (serialize_deviceIDCRI_payload)      x
  == v (len_of_deviceIDCRI_payload
       (x.deviceIDCRI_version)
       (get_RDN_x520_attribute_string x.deviceIDCRI_subject.deviceIDCRI_subject_Common)
       (get_RDN_x520_attribute_string x.deviceIDCRI_subject.deviceIDCRI_subject_Organization)
       (get_RDN_x520_attribute_string x.deviceIDCRI_subject.deviceIDCRI_subject_Country))
)

(*
 *
 *)
let deviceIDCRI_t
= inbound_sequence_value_of (serialize_deviceIDCRI_payload)

let parse_deviceIDCRI
: parser (parse_asn1_envelop_tag_with_TLV_kind SEQUENCE) (deviceIDCRI_t)
= (deviceIDCRI_t)
   `coerce_parser`
  (parse_asn1_sequence_TLV
  (**) (serialize_deviceIDCRI_payload))

let serialize_deviceIDCRI
= coerce_parser_serializer
  (* p *) (parse_deviceIDCRI)
  (* s *) (serialize_asn1_sequence_TLV
          (**) (serialize_deviceIDCRI_payload))
  (*prf*) ()

val lemma_serialize_deviceIDCRI_unfold
  (x: deviceIDCRI_t)
: Lemma ( predicate_serialize_asn1_sequence_TLV_unfold (serialize_deviceIDCRI_payload) x )

val lemma_serialize_deviceIDCRI_size
  (x: deviceIDCRI_t)
: Lemma ( predicate_serialize_asn1_sequence_TLV_size (serialize_deviceIDCRI_payload) x )

// let valid_deviceIDCRI_ingredients
//   (version: datatype_of_asn1_type INTEGER)
//   (s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
//   (s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
//   (s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
//   (ku: key_usage_payload_t)
// : Type0
// = v (len_of_deviceIDCRI_payload version s_common s_org s_country)
//   <= asn1_value_length_max_of_type SEQUENCE

let len_of_deviceIDCRI_max ()
: Tot (asn1_TLV_int32_of_type SEQUENCE)
= len_of_TLV SEQUENCE (len_of_deviceIDCRI_payload_max ())

#push-options "--z3rlimit 256"
let len_of_deviceIDCRI
  (version: datatype_of_asn1_type INTEGER)
  (s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
: Tot (len: asn1_TLV_int32_of_type SEQUENCE
            { v len <= v (len_of_deviceIDCRI_max ()) })
= [@ inline_let]
  let len = len_of_TLV SEQUENCE (len_of_deviceIDCRI_payload version s_common s_org s_country) in
  assert ( v len <= v (len_of_deviceIDCRI_max ()));
  len
#pop-options

val lemma_serialize_deviceIDCRI_size_exact
  (x: deviceIDCRI_t)
      // { let attrs' = coerce_envelop
      //           (CUSTOM_TAG CONTEXT_SPECIFIC CONSTRUCTED 0uy `asn1_implicit_tagging` SET)
      //           (SEQUENCE)
      //           (OID_PKCS9_CSR_EXT_REQ `serialize_envelop_OID_with`
      //           (**) (SET `serialize_asn1_envelop_tag_with_TLV`
      //                (**) (SEQUENCE `serialize_asn1_envelop_tag_with_TLV`
      //                     (**) serialize_deviceIDCRI_attributes_extensionRequest_payload)))
      //           (x.deviceIDCRI_attributes) in
      //   valid_deviceIDCRI_ingredients
      //    (x.deviceIDCRI_version)
      //    (get_RDN_x520_attribute_string x.deviceIDCRI_subject.deviceIDCRI_subject_Common)
      //    (get_RDN_x520_attribute_string x.deviceIDCRI_subject.deviceIDCRI_subject_Organization)
      //    (get_RDN_x520_attribute_string x.deviceIDCRI_subject.deviceIDCRI_subject_Country)
      //    (ku) })
: Lemma (
  let _ = lemma_serialize_deviceIDCRI_size x in
  // let attrs' = coerce_envelop
  //               (CUSTOM_TAG CONTEXT_SPECIFIC CONSTRUCTED 0uy `asn1_implicit_tagging` SET)
  //               (SEQUENCE)
  //               (OID_PKCS9_CSR_EXT_REQ `serialize_envelop_OID_with`
  //               (**) (SET `serialize_asn1_envelop_tag_with_TLV`
  //                    (**) (SEQUENCE `serialize_asn1_envelop_tag_with_TLV`
  //                         (**) serialize_deviceIDCRI_attributes_extensionRequest_payload)))
  //               (x.deviceIDCRI_attributes) in
  length_of_opaque_serialization (serialize_deviceIDCRI) x
  == v (len_of_deviceIDCRI
         (x.deviceIDCRI_version)
         (get_RDN_x520_attribute_string x.deviceIDCRI_subject.deviceIDCRI_subject_Common)
         (get_RDN_x520_attribute_string x.deviceIDCRI_subject.deviceIDCRI_subject_Organization)
         (get_RDN_x520_attribute_string x.deviceIDCRI_subject.deviceIDCRI_subject_Country)) )

(* low *)

noextract inline_for_extraction
val serialize32_deviceIDCRI_payload_backwards
: serializer32_backwards (serialize_deviceIDCRI_payload)

noextract inline_for_extraction
val serialize32_deviceIDCRI_backwards
: serializer32_backwards (serialize_deviceIDCRI)

let x509_get_deviceIDCRI
  (version: datatype_of_asn1_type INTEGER)
  (s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (ku: key_usage_payload_t)
  (deviceIDPub: B32.lbytes32 32ul)
: Tot (deviceIDCRI_t)
=
  let subject: deviceIDCRI_subject_t = x509_get_deviceIDCRI_subject
    #(dfst (s_common <: datatype_of_asn1_type IA5_STRING))
    (dsnd (s_common <: datatype_of_asn1_type IA5_STRING))
    #(dfst (s_org <: datatype_of_asn1_type IA5_STRING))
    (dsnd (s_org <: datatype_of_asn1_type IA5_STRING))
    #(dfst (s_country <: datatype_of_asn1_type PRINTABLE_STRING))
    (dsnd (s_country <: datatype_of_asn1_type PRINTABLE_STRING)) in
  (* Prf *) lemma_serialize_deviceIDCRI_subject_size_exact subject;

  let deviceIDCRI_attributes: deviceIDCRI_attributes_t = x509_get_deviceIDCRI_attributes ku in
  (* Prf *) lemma_serialize_deviceIDCRI_attributes_size_exact deviceIDCRI_attributes;

  let deviceID_PKInfo = x509_get_subjectPublicKeyInfo deviceIDPub in
  (* Prf *) lemma_serialize_subjectPublicKeyInfo_size_exact deviceID_PKInfo;

  let deviceIDCRI: deviceIDCRI_payload_t = {
    deviceIDCRI_version       = version;
    deviceIDCRI_subject       = subject;
    deviceIDCRI_subjectPKInfo = deviceID_PKInfo;
    deviceIDCRI_attributes    = deviceIDCRI_attributes;
  } in
  (* Prf *) lemma_serialize_deviceIDCRI_payload_unfold deviceIDCRI;
  (* Prf *) lemma_serialize_deviceIDCRI_payload_size   deviceIDCRI;

(*return*) deviceIDCRI
