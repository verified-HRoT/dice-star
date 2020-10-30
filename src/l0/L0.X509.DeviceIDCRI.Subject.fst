module L0.X509.DeviceIDCRI.Subject

open ASN1.Spec
open ASN1.Low
open X509
open FStar.Integers

module B32 = FStar.Bytes

#set-options "--z3rlimit 512 --fuel 0 --ifuel 0 --using_facts_from '* -FStar.Tactics -FStar.Reflection'"

#set-options "--__temp_no_proj L0.X509.DeviceIDCRI.Subject"

let decl = ()

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

inline_for_extraction noextract
let synth_deviceIDCRI_subject_payload_t'
  (x: deviceIDCRI_subject_payload_t)
: Tot (x': deviceIDCRI_subject_payload_t'
           { x == synth_deviceIDCRI_subject_payload_t x' })
= (x.deviceIDCRI_subject_Common,
   x.deviceIDCRI_subject_Organization),
   x.deviceIDCRI_subject_Country

let parse_deviceIDCRI_subject_payload
= parse_RDN_x520_attribute COMMON_NAME  IA5_STRING
  `nondep_then`
  parse_RDN_x520_attribute ORGANIZATION IA5_STRING
  `nondep_then`
  parse_RDN_x520_attribute COUNTRY      PRINTABLE_STRING
  `parse_synth`
  synth_deviceIDCRI_subject_payload_t

let serialize_deviceIDCRI_subject_payload
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

let lemma_serialize_deviceIDCRI_subject_payload_unfold x
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

let lemma_serialize_deviceIDCRI_subject_payload_size x
= lemma_serialize_deviceIDCRI_subject_payload_unfold x;
    lemma_serialize_RDN_x520_attribute_size_exact x.deviceIDCRI_subject_Common;
    lemma_serialize_RDN_x520_attribute_size_exact x.deviceIDCRI_subject_Organization;
    lemma_serialize_RDN_x520_attribute_size_exact x.deviceIDCRI_subject_Country

(*
 *
 *)

let lemma_serialize_deviceIDCRI_subject_unfold x
= lemma_serialize_asn1_sequence_TLV_unfold (serialize_deviceIDCRI_subject_payload) x

let lemma_serialize_deviceIDCRI_subject_size x
= lemma_serialize_asn1_sequence_TLV_size (serialize_deviceIDCRI_subject_payload) x

let lemma_serialize_deviceIDCRI_subject_size_exact x
= lemma_serialize_deviceIDCRI_subject_size x;
  (**) lemma_serialize_deviceIDCRI_subject_payload_size x

(* Low *)

let serialize32_deviceIDCRI_subject_payload_backwards
= serialize32_synth_backwards
  (* s32*) (serialize32_RDN_COMMON_NAME
            `serialize32_nondep_then_backwards`
            serialize32_RDN_ORGANIZATION
            `serialize32_nondep_then_backwards`
            serialize32_RDN_COUNTRY)
  (* f2 *) (synth_deviceIDCRI_subject_payload_t)
  (* g1 *) (synth_deviceIDCRI_subject_payload_t')
  (* g1'*) (synth_deviceIDCRI_subject_payload_t')
  (* prf*) ()

let serialize32_deviceIDCRI_subject_backwards
= coerce_serializer32_backwards
  (* s  *) (serialize_deviceIDCRI_subject)
  (* s32*) (serialize32_asn1_sequence_TLV_backwards
           (**) (serialize32_deviceIDCRI_subject_payload_backwards))
  (* prf*) ()
