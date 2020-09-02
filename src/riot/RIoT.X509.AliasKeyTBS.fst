module RIoT.X509.AliasKeyTBS

open ASN1.Spec
open ASN1.Low
open X509
open RIoT.X509.AliasKeyTBS.Issuer
open RIoT.X509.AliasKeyTBS.Subject
open RIoT.X509.AliasKeyTBS.Extensions
open FStar.Integers

module B32 = FStar.Bytes

#set-options "--z3rlimit 256 --fuel 0 --ifuel 0"

type aliasKeyTBS_payload_t = {
(*
 *       version         [0]  EXPLICIT Version DEFAULT v1,
 *)
  aliasKeyTBS_version     : x509_version_t;
(*
 *       serialNumber         CertificateSerialNumber,
 *)
  aliasKeyTBS_serialNumber: datatype_of_asn1_type INTEGER;
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

let aliasKeyTBS_payload_t' = (
(*
 *       version         [0]  EXPLICIT Version DEFAULT v1,
 *)
  x509_version_t `tuple2`
(*
 *       serialNumber         CertificateSerialNumber,
 *)
  datatype_of_asn1_type INTEGER `tuple2`
(*
 *       signature            AlgorithmIdentifier,
 *)
  algorithmIdentifier_t `tuple2`
(*
 *       issuer               Name,
 *)
  aliasKeyTBS_issuer_t `tuple2`
(*
 *       validity             Validity,
 *)
  x509_validity_t `tuple2`
(*
 *       subject              Name,
 *)
  aliasKeyTBS_subject_t `tuple2`
(*
 *      subjectPublicKeyInfo SubjectPublicKeyInfo
 *)
  subjectPublicKeyInfo_t `tuple2`
(*
 *      extensions      [3]  EXPLICIT Extensions OPTIONAL
 *)
  x509_extensions_t_inbound serialize_aliasKeyTBS_extensions
)

let synth_aliasKeyTBS_payload_t
  (x': aliasKeyTBS_payload_t')
: GTot (aliasKeyTBS_payload_t)
= { aliasKeyTBS_version      = fst (fst (fst (fst (fst (fst (fst x'))))));
    aliasKeyTBS_serialNumber = snd (fst (fst (fst (fst (fst (fst x'))))));
    aliasKeyTBS_signatureAlg = snd (fst (fst (fst (fst (fst x')))));
    aliasKeyTBS_issuer       = snd (fst (fst (fst (fst x'))));
    aliasKeyTBS_validity     = snd (fst (fst (fst x')));
    aliasKeyTBS_subject      = snd (fst (fst x'));
    aliasKeyTBS_aliasKey_pub = snd (fst x');
    aliasKeyTBS_extensions   = snd x' }

let synth_aliasKeyTBS_payload_t'
  (x: aliasKeyTBS_payload_t)
: Tot (x': aliasKeyTBS_payload_t' { x == synth_aliasKeyTBS_payload_t x' })
= ((((((x.aliasKeyTBS_version,
        x.aliasKeyTBS_serialNumber),
        x.aliasKeyTBS_signatureAlg),
        x.aliasKeyTBS_issuer),
        x.aliasKeyTBS_validity),
        x.aliasKeyTBS_subject),
        x.aliasKeyTBS_aliasKey_pub),
        x.aliasKeyTBS_extensions

let parse_aliasKeyTBS_payload
: parser _ aliasKeyTBS_payload_t
= parse_x509_version
  `nondep_then`
  parse_asn1_TLV_of_type INTEGER
  `nondep_then`
  parse_algorithmIdentifier
  `nondep_then`
  parse_aliasKeyTBS_issuer
  `nondep_then`
  parse_x509_validity
  `nondep_then`
  parse_aliasKeyTBS_subject
  `nondep_then`
  parse_subjectPublicKeyInfo
  `nondep_then`
  parse_x509_extensions_TLV serialize_aliasKeyTBS_extensions
  `parse_synth`
  synth_aliasKeyTBS_payload_t

let serialize_aliasKeyTBS_payload
: serializer (parse_aliasKeyTBS_payload)
= serialize_synth
  (* p1 *) (parse_x509_version
            `nondep_then`
            parse_asn1_TLV_of_type INTEGER
            `nondep_then`
            parse_algorithmIdentifier
            `nondep_then`
            parse_aliasKeyTBS_issuer
            `nondep_then`
            parse_x509_validity
            `nondep_then`
            parse_aliasKeyTBS_subject
            `nondep_then`
            parse_subjectPublicKeyInfo
            `nondep_then`
            parse_x509_extensions_TLV serialize_aliasKeyTBS_extensions)
  (* f2 *) (synth_aliasKeyTBS_payload_t)
  (* s1 *) (serialize_x509_version
            `serialize_nondep_then`
            serialize_asn1_TLV_of_type INTEGER
            `serialize_nondep_then`
            serialize_algorithmIdentifier
            `serialize_nondep_then`
            serialize_aliasKeyTBS_issuer
            `serialize_nondep_then`
            serialize_x509_validity
            `serialize_nondep_then`
            serialize_aliasKeyTBS_subject
            `serialize_nondep_then`
            serialize_subjectPublicKeyInfo
            `serialize_nondep_then`
            serialize_x509_extensions_TLV serialize_aliasKeyTBS_extensions)
  (* g1 *) (synth_aliasKeyTBS_payload_t')
  (* prf*) ()

let lemma_serialize_aliasKeyTBS_payload_unfold
  (x: aliasKeyTBS_payload_t)
: Lemma (
  serialize_aliasKeyTBS_payload `serialize` x ==
 (serialize_x509_version `serialize` x.aliasKeyTBS_version)
  `Seq.append`
 (serialize_asn1_TLV_of_type INTEGER `serialize` x.aliasKeyTBS_serialNumber)
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
=
  serialize_nondep_then_eq
  (* s1 *) (serialize_x509_version)
  (* s2 *) (serialize_asn1_TLV_of_type INTEGER)
  (* in *) (fst (fst (fst(fst (fst (fst (synth_aliasKeyTBS_payload_t' x)))))));

  serialize_nondep_then_eq
  (* s1 *) (serialize_x509_version
            `serialize_nondep_then`
            serialize_asn1_TLV_of_type INTEGER)
  (* s2 *) (serialize_algorithmIdentifier)
  (* in *) (fst (fst(fst (fst (fst (synth_aliasKeyTBS_payload_t' x))))));

  serialize_nondep_then_eq
  (* s1 *) (serialize_x509_version
            `serialize_nondep_then`
            serialize_asn1_TLV_of_type INTEGER
            `serialize_nondep_then`
            serialize_algorithmIdentifier)
  (* s2 *) (serialize_aliasKeyTBS_issuer)
  (* in *) (fst (fst (fst (fst (synth_aliasKeyTBS_payload_t' x)))));

  serialize_nondep_then_eq
  (* s1 *) (serialize_x509_version
            `serialize_nondep_then`
            serialize_asn1_TLV_of_type INTEGER
            `serialize_nondep_then`
            serialize_algorithmIdentifier
            `serialize_nondep_then`
            serialize_aliasKeyTBS_issuer)
  (* s2 *) (serialize_x509_validity)
  (* in *) (fst (fst (fst (synth_aliasKeyTBS_payload_t' x))));

  serialize_nondep_then_eq
  (* s1 *) (serialize_x509_version
            `serialize_nondep_then`
            serialize_asn1_TLV_of_type INTEGER
            `serialize_nondep_then`
            serialize_algorithmIdentifier
            `serialize_nondep_then`
            serialize_aliasKeyTBS_issuer
            `serialize_nondep_then`
            serialize_x509_validity)
  (* s2 *) (serialize_aliasKeyTBS_subject)
  (* in *) (fst (fst (synth_aliasKeyTBS_payload_t' x)));

  serialize_nondep_then_eq
  (* s1 *) (serialize_x509_version
            `serialize_nondep_then`
            serialize_asn1_TLV_of_type INTEGER
            `serialize_nondep_then`
            serialize_algorithmIdentifier
            `serialize_nondep_then`
            serialize_aliasKeyTBS_issuer
            `serialize_nondep_then`
            serialize_x509_validity
            `serialize_nondep_then`
            serialize_aliasKeyTBS_subject)
  (* s2 *) (serialize_subjectPublicKeyInfo)
  (* in *) (fst (synth_aliasKeyTBS_payload_t' x));

  serialize_nondep_then_eq
  (* s1 *) (serialize_x509_version
            `serialize_nondep_then`
            serialize_asn1_TLV_of_type INTEGER
            `serialize_nondep_then`
            serialize_algorithmIdentifier
            `serialize_nondep_then`
            serialize_aliasKeyTBS_issuer
            `serialize_nondep_then`
            serialize_x509_validity
            `serialize_nondep_then`
            serialize_aliasKeyTBS_subject
            `serialize_nondep_then`
            serialize_subjectPublicKeyInfo)
  (* s2 *) (serialize_x509_extensions_TLV serialize_aliasKeyTBS_extensions)
  (* in *) (synth_aliasKeyTBS_payload_t' x);

  serialize_synth_eq
  (* p1 *) (parse_x509_version
            `nondep_then`
            parse_asn1_TLV_of_type INTEGER
            `nondep_then`
            parse_algorithmIdentifier
            `nondep_then`
            parse_aliasKeyTBS_issuer
            `nondep_then`
            parse_x509_validity
            `nondep_then`
            parse_aliasKeyTBS_subject
            `nondep_then`
            parse_subjectPublicKeyInfo
            `nondep_then`
            parse_x509_extensions_TLV serialize_aliasKeyTBS_extensions)
  (* f2 *) (synth_aliasKeyTBS_payload_t)
  (* s1 *) (serialize_x509_version
            `serialize_nondep_then`
            serialize_asn1_TLV_of_type INTEGER
            `serialize_nondep_then`
            serialize_algorithmIdentifier
            `serialize_nondep_then`
            serialize_aliasKeyTBS_issuer
            `serialize_nondep_then`
            serialize_x509_validity
            `serialize_nondep_then`
            serialize_aliasKeyTBS_subject
            `serialize_nondep_then`
            serialize_subjectPublicKeyInfo
            `serialize_nondep_then`
            serialize_x509_extensions_TLV serialize_aliasKeyTBS_extensions)
  (* g1 *) (synth_aliasKeyTBS_payload_t')
  (* prf*) ()
  (* in *) (x)

let length_of_aliasKeyTBS_payload
  (serialNumber: datatype_of_asn1_type INTEGER)
  (i_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (i_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (i_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (ku: key_usage_payload_t)
  (version: datatype_of_asn1_type INTEGER)
: GTot (nat)
= length_of_x509_version () +
  length_of_asn1_primitive_TLV serialNumber +
  length_of_algorithmIdentifier () +
  length_of_aliasKeyTBS_issuer i_common i_org i_country +
  length_of_x509_validity () +
  length_of_aliasKeyTBS_subject s_common s_org s_country +
  length_of_subjectPublicKeyInfo +
  length_of_x509_extensions (length_of_aliasKeyTBS_extensions ku version)

let len_of_aliasKeyTBS_payload
  (serialNumber: datatype_of_asn1_type INTEGER)
  (i_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (i_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (i_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (ku: key_usage_payload_t)
  (version: datatype_of_asn1_type INTEGER
            { length_of_aliasKeyTBS_payload
                serialNumber
                i_common i_org i_country
                s_common s_org s_country
                ku version
              <= asn1_value_length_max_of_type SEQUENCE })
: Tot (len: asn1_TLV_int32_of_type SEQUENCE
            { v len == length_of_aliasKeyTBS_payload
                         serialNumber
                         i_common i_org i_country
                         s_common s_org s_country
                         ku version })
= len_of_x509_version () +
  len_of_asn1_primitive_TLV serialNumber +
  len_of_algorithmIdentifier () +
  len_of_aliasKeyTBS_issuer i_common i_org i_country +
  len_of_x509_validity () +
  len_of_aliasKeyTBS_subject s_common s_org s_country +
  len_of_subjectPublicKeyInfo +
  len_of_x509_extensions (len_of_aliasKeyTBS_extensions ku version)

#restart-solver
#push-options "--z3rlimit 512"
let lemma_serialize_aliasKeyTBS_payload_size
  (x: aliasKeyTBS_payload_t)
: Lemma (
  let riot_version = RIoT.X509.Extension.(x.aliasKeyTBS_extensions.aliasKeyTBS_extensions_riot.x509_extValue_riot.riot_version) in
  let ku = (snd x.aliasKeyTBS_extensions.aliasKeyTBS_extensions_key_usage) in
  (* unfold *)
  length_of_opaque_serialization (serialize_aliasKeyTBS_payload) x ==
  length_of_opaque_serialization (serialize_x509_version)             x.aliasKeyTBS_version      +
  length_of_opaque_serialization (serialize_asn1_TLV_of_type INTEGER) x.aliasKeyTBS_serialNumber +
  length_of_opaque_serialization (serialize_algorithmIdentifier)      x.aliasKeyTBS_signatureAlg +
  length_of_opaque_serialization (serialize_aliasKeyTBS_issuer)       x.aliasKeyTBS_issuer     +
  length_of_opaque_serialization (serialize_x509_validity)            x.aliasKeyTBS_validity     +
  length_of_opaque_serialization (serialize_aliasKeyTBS_subject)      x.aliasKeyTBS_subject     +
  length_of_opaque_serialization (serialize_subjectPublicKeyInfo)     x.aliasKeyTBS_aliasKey_pub +
  length_of_opaque_serialization (serialize_x509_extensions_TLV
                                  serialize_aliasKeyTBS_extensions)   x.aliasKeyTBS_extensions /\
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
       ku
       riot_version
)
= lemma_serialize_aliasKeyTBS_payload_unfold x;
    lemma_serialize_x509_version_size_exact x.aliasKeyTBS_version;
    lemma_serialize_asn1_integer_TLV_size x.aliasKeyTBS_serialNumber;
    lemma_serialize_algorithmIdentifier_size_exact x.aliasKeyTBS_signatureAlg;
    lemma_serialize_aliasKeyTBS_issuer_size_exact x.aliasKeyTBS_issuer;
    lemma_serialize_x509_validity_size_exact x.aliasKeyTBS_validity;
    lemma_serialize_aliasKeyTBS_subject_size_exact x.aliasKeyTBS_subject;
    lemma_serialize_subjectPublicKeyInfo_size_exact x.aliasKeyTBS_aliasKey_pub;
    lemma_serialize_x509_extensions_TLV_size serialize_aliasKeyTBS_extensions x.aliasKeyTBS_extensions;
      lemma_serialize_aliasKeyTBS_extensions_size_exact x.aliasKeyTBS_extensions
#pop-options

let aliasKeyTBS_t
= inbound_sequence_value_of (serialize_aliasKeyTBS_payload)

let parse_aliasKeyTBS
: parser (parse_asn1_envelop_tag_with_TLV_kind SEQUENCE) (aliasKeyTBS_t)
=
  aliasKeyTBS_t
  `coerce_parser`
  parse_asn1_sequence_TLV (serialize_aliasKeyTBS_payload)

let serialize_aliasKeyTBS
: serializer (parse_aliasKeyTBS)
= coerce_parser_serializer
    (parse_aliasKeyTBS)
    (serialize_asn1_sequence_TLV (serialize_aliasKeyTBS_payload))
    ()

let lemma_serialize_aliasKeyTBS_unfold
  (x: aliasKeyTBS_t)
: Lemma ( predicate_serialize_asn1_sequence_TLV_unfold (serialize_aliasKeyTBS_payload) x )
= lemma_serialize_asn1_sequence_TLV_unfold (serialize_aliasKeyTBS_payload) x

let lemma_serialize_aliasKeyTBS_size
  (x: aliasKeyTBS_t)
: Lemma ( predicate_serialize_asn1_sequence_TLV_size (serialize_aliasKeyTBS_payload) x )
= lemma_serialize_asn1_sequence_TLV_size (serialize_aliasKeyTBS_payload) x

let length_of_aliasKeyTBS
  (serialNumber: datatype_of_asn1_type INTEGER)
  (i_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (i_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (i_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (ku: key_usage_payload_t)
  (version: datatype_of_asn1_type INTEGER
            { length_of_aliasKeyTBS_payload
                serialNumber
                i_common i_org i_country
                s_common s_org s_country
                ku version
              <= asn1_value_length_max_of_type SEQUENCE })
: GTot (asn1_TLV_length_of_type SEQUENCE)
= length_of_TLV
    (SEQUENCE)
    (length_of_aliasKeyTBS_payload
      serialNumber
      i_common i_org i_country
      s_common s_org s_country
      ku version)

#restart-solver
let len_of_aliasKeyTBS
  (serialNumber: datatype_of_asn1_type INTEGER)
  (i_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (i_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (i_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (ku: key_usage_payload_t)
  (version: datatype_of_asn1_type INTEGER
            { length_of_aliasKeyTBS_payload
                serialNumber
                i_common i_org i_country
                s_common s_org s_country
                ku version
              <= asn1_value_length_max_of_type SEQUENCE })
// : Tot (len: asn1_TLV_length_of_type SEQUENCE
//              { v len == length_of_aliasKeyTBS
//                           serialNumber
//                           i_common i_org i_country
//                           s_common s_org s_country
//                           ku version })
= len_of_TLV
    (SEQUENCE)
    (len_of_aliasKeyTBS_payload
      serialNumber
      i_common i_org i_country
      s_common s_org s_country
      ku version)

#restart-solver
#push-options "--z3rlimit 512"
let lemma_serialize_aliasKeyTBS_size_exact
  (x: aliasKeyTBS_t)
: Lemma (
  let riot_version = RIoT.X509.Extension.(x.aliasKeyTBS_extensions.aliasKeyTBS_extensions_riot.x509_extValue_riot.riot_version) in
  let ku = (snd x.aliasKeyTBS_extensions.aliasKeyTBS_extensions_key_usage) in
  let _ = lemma_serialize_aliasKeyTBS_payload_size x in
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
       ku
       riot_version
)
= lemma_serialize_aliasKeyTBS_size x;
    lemma_serialize_aliasKeyTBS_payload_size x
#pop-options

(* low *)
let serialize32_aliasKeyTBS_payload_backwards
: serializer32_backwards (serialize_aliasKeyTBS_payload)
= serialize32_synth_backwards
  (* s1 *) (serialize32_x509_version_backwards
            `serialize32_nondep_then_backwards`
            serialize32_asn1_TLV_backwards_of_type INTEGER
            `serialize32_nondep_then_backwards`
            serialize32_algorithmIdentifier_backwards
            `serialize32_nondep_then_backwards`
            serialize32_aliasKeyTBS_issuer_backwards
            `serialize32_nondep_then_backwards`
            serialize32_x509_validity_backwards
            `serialize32_nondep_then_backwards`
            serialize32_aliasKeyTBS_subject_backwards
            `serialize32_nondep_then_backwards`
            serialize32_subjectPublicKeyInfo_backwards
            `serialize32_nondep_then_backwards`
            serialize32_x509_extensions_TLV_backwards serialize32_aliasKeyTBS_extensions_backwards)
  (* f2 *) (synth_aliasKeyTBS_payload_t)
  (* g1 *) (synth_aliasKeyTBS_payload_t')
  (* g1'*) (synth_aliasKeyTBS_payload_t')
  (* prf*) ()

let serialize32_aliasKeyTBS_backwards
: serializer32_backwards (serialize_aliasKeyTBS)
= coerce_serializer32_backwards
  (* s2 *) (serialize_aliasKeyTBS)
  (* s32*) (serialize32_asn1_sequence_TLV_backwards
             (serialize32_aliasKeyTBS_payload_backwards))
  (* prf*) ()


(* helpers *)
#restart-solver
let x509_get_AliasKeyTBS
  (crt_version: x509_version_t)
  (serialNumber: datatype_of_asn1_type INTEGER)
  (i_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (i_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (i_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING
              { length_of_aliasKeyTBS_issuer_payload i_common i_org i_country
                <= asn1_value_length_max_of_type SEQUENCE })
  (notBefore: datatype_of_asn1_type Generalized_Time)
  (notAfter : datatype_of_asn1_type Generalized_Time)
  (s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (ku: key_usage_payload_t)
  (version: datatype_of_asn1_type INTEGER
            { length_of_aliasKeyTBS_payload
                serialNumber
                i_common i_org i_country
                s_common s_org s_country
                ku version
              <= asn1_value_length_max_of_type SEQUENCE })
  (fwid: B32.lbytes32 32ul)
  (deviceIDPub: B32.lbytes32 32ul)
  (aliasKeyPub: B32.lbytes32 32ul)
: Tot (aliasKeyTBS_t)
=
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
  (* Prf *) (**) lemma_serialize_asn1_integer_TLV_size serialNumber;

(*return*) aliasKeyTBS
