module L0.X509.DeviceIDCRI

open ASN1.Spec
open ASN1.Low
open X509
open RIoT.X509.DeviceIDCRI.Subject
open RIoT.X509.DeviceIDCRI.Attributes
open FStar.Integers

module B32 = FStar.Bytes

#set-options "--z3rlimit 256 --fuel 0 --ifuel 0"

#set-options "--__temp_no_proj RIoT.X509.DeviceIDCRI"

let decl = ()

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

let deviceIDCRI_payload_t' = (
  datatype_of_asn1_type INTEGER `tuple2`
  deviceIDCRI_subject_t `tuple2`
  subjectPublicKeyInfo_t `tuple2`
  deviceIDCRI_attributes_t
)


(* Conversion *)
let synth_deviceIDCRI_payload_t
  (x': deviceIDCRI_payload_t')
: GTot (deviceIDCRI_payload_t) = {
  deviceIDCRI_version       = fst (fst (fst x'));
  deviceIDCRI_subject       = snd (fst (fst x'));
  deviceIDCRI_subjectPKInfo = snd (fst x');
  deviceIDCRI_attributes    = snd x';
}

inline_for_extraction noextract
let synth_deviceIDCRI_payload_t'
  (x: deviceIDCRI_payload_t)
: Tot (x': deviceIDCRI_payload_t'
            { x == synth_deviceIDCRI_payload_t x' }) = (
  (((x.deviceIDCRI_version),
     x.deviceIDCRI_subject),
     x.deviceIDCRI_subjectPKInfo),
     x.deviceIDCRI_attributes
)


(*
 * Specification
 *)
let parse_deviceIDCRI_payload
= parse_asn1_TLV_of_type INTEGER
  `nondep_then`
  parse_deviceIDCRI_subject
  `nondep_then`
  parse_subjectPublicKeyInfo
  `nondep_then`
  parse_deviceIDCRI_attributes
  `parse_synth`
  synth_deviceIDCRI_payload_t

let serialize_deviceIDCRI_payload
= serialize_synth
  (* p1 *) (parse_asn1_TLV_of_type INTEGER
            `nondep_then`
            parse_deviceIDCRI_subject
            `nondep_then`
            parse_subjectPublicKeyInfo
            `nondep_then`
            parse_deviceIDCRI_attributes)
  (* f2 *) (synth_deviceIDCRI_payload_t)
  (* s1 *) (serialize_asn1_TLV_of_type INTEGER
            `serialize_nondep_then`
            serialize_deviceIDCRI_subject
            `serialize_nondep_then`
            serialize_subjectPublicKeyInfo
            `serialize_nondep_then`
            serialize_deviceIDCRI_attributes)
  (* g1 *) (synth_deviceIDCRI_payload_t')
  (* prf*) ()

let lemma_serialize_deviceIDCRI_payload_unfold x
= serialize_nondep_then_eq
  (* s1 *) (serialize_asn1_TLV_of_type INTEGER)
  (* s2 *) (serialize_deviceIDCRI_subject)
  (* in *) (fst (fst (synth_deviceIDCRI_payload_t' x)));
  serialize_nondep_then_eq
  (* s1 *) (serialize_asn1_TLV_of_type INTEGER
            `serialize_nondep_then`
            serialize_deviceIDCRI_subject)
  (* s2 *) (serialize_subjectPublicKeyInfo)
  (* in *) (fst (synth_deviceIDCRI_payload_t' x));
  serialize_nondep_then_eq
  (* s1 *) (serialize_asn1_TLV_of_type INTEGER
            `serialize_nondep_then`
            serialize_deviceIDCRI_subject
            `serialize_nondep_then`
            serialize_subjectPublicKeyInfo)
  (* s2 *) (serialize_deviceIDCRI_attributes)
  (* in *) (synth_deviceIDCRI_payload_t' x);
  serialize_synth_eq
  (* p1 *) (parse_asn1_TLV_of_type INTEGER
            `nondep_then`
            parse_deviceIDCRI_subject
            `nondep_then`
            parse_subjectPublicKeyInfo
            `nondep_then`
            parse_deviceIDCRI_attributes)
  (* f2 *) (synth_deviceIDCRI_payload_t)
  (* s1 *) (serialize_asn1_TLV_of_type INTEGER
            `serialize_nondep_then`
            serialize_deviceIDCRI_subject
            `serialize_nondep_then`
            serialize_subjectPublicKeyInfo
            `serialize_nondep_then`
            serialize_deviceIDCRI_attributes)
  (* g1 *) (synth_deviceIDCRI_payload_t')
  (* prf*) ()
  (* in *) (x)

let lemma_serialize_deviceIDCRI_payload_size x
= lemma_serialize_deviceIDCRI_payload_unfold x;
    lemma_serialize_deviceIDCRI_subject_size_exact    x.deviceIDCRI_subject;
    lemma_serialize_subjectPublicKeyInfo_size_exact   x.deviceIDCRI_subjectPKInfo;
    lemma_serialize_deviceIDCRI_attributes_size_exact x.deviceIDCRI_attributes

(*
 *
 *)

let lemma_serialize_deviceIDCRI_unfold x
= lemma_serialize_asn1_sequence_TLV_unfold (serialize_deviceIDCRI_payload) x

let lemma_serialize_deviceIDCRI_size x
= lemma_serialize_asn1_sequence_TLV_size (serialize_deviceIDCRI_payload) x

let lemma_serialize_deviceIDCRI_size_exact x
= lemma_serialize_deviceIDCRI_size x;
  (**) lemma_serialize_deviceIDCRI_payload_size x

(* low *)
let serialize32_deviceIDCRI_payload_backwards
= serialize32_synth_backwards
  (* s32*) (serialize32_asn1_TLV_backwards_of_type INTEGER
            `serialize32_nondep_then_backwards`
            serialize32_deviceIDCRI_subject_backwards
            `serialize32_nondep_then_backwards`
            serialize32_subjectPublicKeyInfo_backwards
            `serialize32_nondep_then_backwards`
            serialize32_deviceIDCRI_attributes_backwards)
  (* f2 *) (synth_deviceIDCRI_payload_t)
  (* g1 *) (synth_deviceIDCRI_payload_t')
  (* g1'*) (synth_deviceIDCRI_payload_t')
  (* prf*) ()

let serialize32_deviceIDCRI_backwards
= coerce_serializer32_backwards
    (serialize_deviceIDCRI)
    (serialize32_asn1_sequence_TLV_backwards
      (serialize32_deviceIDCRI_payload_backwards))
    ()
