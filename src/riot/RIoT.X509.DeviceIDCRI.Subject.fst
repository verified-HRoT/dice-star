module RIoT.X509.DeviceIDCRI.Subject

open ASN1.Spec
open ASN1.Low
open X509
open FStar.Integers

module B32 = FStar.Bytes

#set-options "--z3rlimit 32 --fuel 0 --ifuel 0"

type deviceIDCRI_subject_payload_t = {
  deviceIDCRI_subject_Common      : x509_RDN_x520_attribute_t COMMON_NAME  IA5_STRING;
  deviceIDCRI_subject_Organization: x509_RDN_x520_attribute_t ORGANIZATION IA5_STRING;
  deviceIDCRI_subject_Country     : x509_RDN_x520_attribute_t COUNTRY      PRINTABLE_STRING
}

let deviceIDCRI_subject_payload_t' = (
  x509_RDN_x520_attribute_t COMMON_NAME  IA5_STRING `tuple2`
  x509_RDN_x520_attribute_t ORGANIZATION IA5_STRING `tuple2`
  x509_RDN_x520_attribute_t COUNTRY      PRINTABLE_STRING
)

let synth_deviceIDCRI_subject_payload_t
  (x': deviceIDCRI_subject_payload_t')
: GTot (deviceIDCRI_subject_payload_t)
= { deviceIDCRI_subject_Common       = fst (fst x');
    deviceIDCRI_subject_Organization = snd (fst x');
    deviceIDCRI_subject_Country      = snd x' }

let synth_deviceIDCRI_subject_payload_t'
  (x: deviceIDCRI_subject_payload_t)
: Tot (x': deviceIDCRI_subject_payload_t'
           { x == synth_deviceIDCRI_subject_payload_t x' })
= (x.deviceIDCRI_subject_Common,
   x.deviceIDCRI_subject_Organization),
   x.deviceIDCRI_subject_Country

let parse_deviceIDCRI_subject_payload
: parser _ (deviceIDCRI_subject_payload_t)
= parse_RDN_x520_attribute COMMON_NAME  IA5_STRING
  `nondep_then`
  parse_RDN_x520_attribute ORGANIZATION IA5_STRING
  `nondep_then`
  parse_RDN_x520_attribute COUNTRY      PRINTABLE_STRING
  `parse_synth`
  synth_deviceIDCRI_subject_payload_t

let serialize_deviceIDCRI_subject_payload
: serializer (parse_deviceIDCRI_subject_payload)
= serialize_synth
  (* p1 *) (parse_RDN_x520_attribute COMMON_NAME  IA5_STRING
            `nondep_then`
            parse_RDN_x520_attribute ORGANIZATION IA5_STRING
            `nondep_then`
            parse_RDN_x520_attribute COUNTRY      PRINTABLE_STRING)
  (* f2 *) (synth_deviceIDCRI_subject_payload_t)
  (* s1 *) (serialize_RDN_x520_attribute COMMON_NAME  IA5_STRING
            `serialize_nondep_then`
            serialize_RDN_x520_attribute ORGANIZATION IA5_STRING
            `serialize_nondep_then`
            serialize_RDN_x520_attribute COUNTRY      PRINTABLE_STRING)
  (* g1 *) (synth_deviceIDCRI_subject_payload_t')
  (* prf*) ()

#push-options "--z3rlimit 64"
let length_of_deviceIDCRI_subject_payload
  (s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
: GTot (nat)
= length_of_RDN_x520_attribute s_common +
  length_of_RDN_x520_attribute s_org +
  length_of_RDN_x520_attribute s_country

let len_of_deviceIDCRI_subject_payload
  (s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING
              { length_of_deviceIDCRI_subject_payload s_common s_org s_country
                <= asn1_value_length_max_of_type SEQUENCE })
: Tot (len: asn1_value_int32_of_type SEQUENCE
            { v len == length_of_deviceIDCRI_subject_payload s_common s_org s_country })
= len_of_RDN_x520_attribute s_common +
  len_of_RDN_x520_attribute s_org +
  len_of_RDN_x520_attribute s_country
#pop-options

let lemma_serialize_deviceIDCRI_subject_payload_unfold
  (x: deviceIDCRI_subject_payload_t)
: Lemma (
  serialize_deviceIDCRI_subject_payload `serialize` x ==
 (serialize_RDN_x520_attribute COMMON_NAME  IA5_STRING `serialize` x.deviceIDCRI_subject_Common)
  `Seq.append`
 (serialize_RDN_x520_attribute ORGANIZATION IA5_STRING `serialize` x.deviceIDCRI_subject_Organization)
  `Seq.append`
 (serialize_RDN_x520_attribute COUNTRY PRINTABLE_STRING `serialize` x.deviceIDCRI_subject_Country)
)
= serialize_nondep_then_eq
  (* s1 *) (serialize_RDN_x520_attribute COMMON_NAME  IA5_STRING)
  (* s2 *) (serialize_RDN_x520_attribute ORGANIZATION IA5_STRING)
  (* in *) (fst (synth_deviceIDCRI_subject_payload_t' x));
  serialize_nondep_then_eq
  (* s1 *) (serialize_RDN_x520_attribute COMMON_NAME  IA5_STRING
            `serialize_nondep_then`
            serialize_RDN_x520_attribute ORGANIZATION IA5_STRING)
  (* s2 *) (serialize_RDN_x520_attribute COUNTRY      PRINTABLE_STRING)
  (* in *) (synth_deviceIDCRI_subject_payload_t' x);
  serialize_synth_eq
  (* p1 *) (parse_RDN_x520_attribute COMMON_NAME  IA5_STRING
            `nondep_then`
            parse_RDN_x520_attribute ORGANIZATION IA5_STRING
            `nondep_then`
            parse_RDN_x520_attribute COUNTRY      PRINTABLE_STRING)
  (* f2 *) (synth_deviceIDCRI_subject_payload_t)
  (* s1 *) (serialize_RDN_x520_attribute COMMON_NAME  IA5_STRING
            `serialize_nondep_then`
            serialize_RDN_x520_attribute ORGANIZATION IA5_STRING
            `serialize_nondep_then`
            serialize_RDN_x520_attribute COUNTRY      PRINTABLE_STRING)
  (* g1 *) (synth_deviceIDCRI_subject_payload_t')
  (* prf*) ()
  (* in *) (x)

let lemma_serialize_deviceIDCRI_subject_payload_size
  (x: deviceIDCRI_subject_payload_t)
: Lemma (
  length_of_opaque_serialization (serialize_deviceIDCRI_subject_payload) x
  == length_of_opaque_serialization (serialize_RDN_x520_attribute _ _) x.deviceIDCRI_subject_Common +
     length_of_opaque_serialization (serialize_RDN_x520_attribute _ _) x.deviceIDCRI_subject_Organization +
     length_of_opaque_serialization (serialize_RDN_x520_attribute _ _) x.deviceIDCRI_subject_Country /\
  length_of_opaque_serialization (serialize_deviceIDCRI_subject_payload) x
  == length_of_deviceIDCRI_subject_payload
       (get_RDN_x520_attribute_string x.deviceIDCRI_subject_Common)
       (get_RDN_x520_attribute_string x.deviceIDCRI_subject_Organization)
       (get_RDN_x520_attribute_string x.deviceIDCRI_subject_Country)
)
= lemma_serialize_deviceIDCRI_subject_payload_unfold x;
    lemma_serialize_RDN_x520_attribute_size_exact x.deviceIDCRI_subject_Common;
    lemma_serialize_RDN_x520_attribute_size_exact x.deviceIDCRI_subject_Organization;
    lemma_serialize_RDN_x520_attribute_size_exact x.deviceIDCRI_subject_Country

(*
 *
 *)

let deviceIDCRI_subject_t
= inbound_sequence_value_of (serialize_deviceIDCRI_subject_payload)

let parse_deviceIDCRI_subject
: parser (parse_asn1_envelop_tag_with_TLV_kind SEQUENCE) (deviceIDCRI_subject_t)
= (deviceIDCRI_subject_t)
  `coerce_parser`
  (parse_asn1_sequence_TLV
   (**) (serialize_deviceIDCRI_subject_payload))

let serialize_deviceIDCRI_subject
: serializer (parse_deviceIDCRI_subject)
= coerce_parser_serializer
  (* p *) (parse_deviceIDCRI_subject)
  (* s *) (serialize_asn1_sequence_TLV
          (**) (serialize_deviceIDCRI_subject_payload))
  (*prf*) ()

#push-options "--z3rlimit 64"
let length_of_deviceIDCRI_subject
  (s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING
              { length_of_deviceIDCRI_subject_payload s_common s_org s_country
                <= asn1_value_length_max_of_type SEQUENCE })
: GTot (asn1_TLV_length_of_type SEQUENCE)
= SEQUENCE `length_of_TLV`
  (**) (length_of_deviceIDCRI_subject_payload s_common s_org s_country)

let len_of_deviceIDCRI_subject
  (s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING
              { length_of_deviceIDCRI_subject_payload s_common s_org s_country
                <= asn1_value_length_max_of_type SEQUENCE })
: Tot (len: asn1_TLV_int32_of_type SEQUENCE
            { v len == length_of_deviceIDCRI_subject s_common s_org s_country })
= SEQUENCE `len_of_TLV`
  (**) (len_of_deviceIDCRI_subject_payload s_common s_org s_country)
#pop-options

let lemma_serialize_deviceIDCRI_subject_unfold
  (x: deviceIDCRI_subject_t)
: Lemma ( predicate_serialize_asn1_sequence_TLV_unfold (serialize_deviceIDCRI_subject_payload) x )
= lemma_serialize_asn1_sequence_TLV_unfold (serialize_deviceIDCRI_subject_payload) x

let lemma_serialize_deviceIDCRI_subject_size
  (x: deviceIDCRI_subject_t)
: Lemma ( predicate_serialize_asn1_sequence_TLV_size (serialize_deviceIDCRI_subject_payload) x )
= lemma_serialize_asn1_sequence_TLV_size (serialize_deviceIDCRI_subject_payload) x

let lemma_serialize_deviceIDCRI_subject_size_exact
  (x: deviceIDCRI_subject_t)
: Lemma (
  let _ = lemma_serialize_deviceIDCRI_subject_payload_size x in
  length_of_opaque_serialization (serialize_deviceIDCRI_subject) x
  == length_of_deviceIDCRI_subject
       (get_RDN_x520_attribute_string x.deviceIDCRI_subject_Common)
       (get_RDN_x520_attribute_string x.deviceIDCRI_subject_Organization)
       (get_RDN_x520_attribute_string x.deviceIDCRI_subject_Country)
)
= lemma_serialize_deviceIDCRI_subject_size x;
  (**) lemma_serialize_deviceIDCRI_subject_payload_size x

(* Low *)

noextract inline_for_extraction
let serialize32_deviceIDCRI_subject_payload_backwards
: serializer32_backwards (serialize_deviceIDCRI_subject_payload)
= serialize32_synth_backwards
  (* s32*) (serialize32_RDN_x520_attribute_backwards COMMON_NAME  IA5_STRING
            `serialize32_nondep_then_backwards`
            serialize32_RDN_x520_attribute_backwards ORGANIZATION IA5_STRING
            `serialize32_nondep_then_backwards`
            serialize32_RDN_x520_attribute_backwards COUNTRY      PRINTABLE_STRING)
  (* f2 *) (synth_deviceIDCRI_subject_payload_t)
  (* g1 *) (synth_deviceIDCRI_subject_payload_t')
  (* g1'*) (synth_deviceIDCRI_subject_payload_t')
  (* prf*) ()

noextract inline_for_extraction
let serialize32_deviceIDCRI_subject_backwards
: serializer32_backwards (serialize_deviceIDCRI_subject)
= coerce_serializer32_backwards
  (* s  *) (serialize_deviceIDCRI_subject)
  (* s32*) (serialize32_asn1_sequence_TLV_backwards
           (**) (serialize32_deviceIDCRI_subject_payload_backwards))
  (* prf*) ()

(*
 *
 *)

#push-options "--z3rlimit 128"
let x509_get_deviceIDCRI_subject
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
: Tot (deviceIDCRI_subject_t)
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
