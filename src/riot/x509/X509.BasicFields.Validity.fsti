module X509.BasicFields.Validity

open ASN1.Spec
open ASN1.Low

open X509.Base

open FStar.Integers

(*
 4.1.2.5.  Validity

   The certificate validity period is the time interval during which the
   CA warrants that it will maintain information about the status of the
   certificate.  The field is represented as a SEQUENCE of two dates:
   the date on which the certificate validity period begins (notBefore)
   and the date on which the certificate validity period ends
   (notAfter).  Both notBefore and notAfter may be encoded as UTCTime or
   GeneralizedTime.

   CAs conforming to this profile MUST always encode certificate
   validity dates through the year 2049 as UTCTime; certificate validity
   dates in 2050 or later MUST be encoded as GeneralizedTime.
   Conforming applications MUST be able to process validity dates that
   are encoded in either UTCTime or GeneralizedTime.

   The validity period for a certificate is the period of time from
   notBefore through notAfter, inclusive.

   In some situations, devices are given certificates for which no good
   expiration date can be assigned.  For example, a device could be
   issued a certificate that binds its model and serial number to its
   public key; such a certificate is intended to be used for the entire
   lifetime of the device.

   To indicate that a certificate has no well-defined expiration date,
   the notAfter SHOULD be assigned the GeneralizedTime value of
   99991231235959Z.
*)

module HS = FStar.HyperStack
module IB = LowStar.ImmutableBuffer

val x509_validity_notAfter_default_buffer
: b: IB.libuffer byte 15 asn1_generalized_time_for_x509_validity_notAfter_default_seq
  { IB.frameOf b == HS.root /\
    IB.recallable b }

type x509_validity_payload_t: Type = {
  notBefore: generalized_time_t;
  notAfter: generalized_time_t
}

let x509_validity_payload_t' = (
  generalized_time_t `tuple2`
  generalized_time_t
)

let synth_x509_validity_payload
  (x: x509_validity_payload_t')
: GTot (x509_validity_payload_t)
= { notBefore = fst x;
    notAfter  = snd x }

let synth_x509_validity_payload'
  (x: x509_validity_payload_t)
: Tot (x': x509_validity_payload_t'
           { x == synth_x509_validity_payload x' })
= ( x.notBefore,
    x.notAfter )

noextract
val parse_x509_validity_payload
: parser (and_then_kind (parse_asn1_TLV_kind_of_type (Generalized_Time))
        (parse_asn1_TLV_kind_of_type (Generalized_Time))) x509_validity_payload_t

noextract
val serialize_x509_validity_payload
: serializer parse_x509_validity_payload

val lemma_x509_validity_payload_unfold
  (x: x509_validity_payload_t)
: Lemma (
  serialize_x509_validity_payload `serialize` x ==
 (serialize_asn1_TLV_of_type Generalized_Time `serialize` x.notBefore)
  `Seq.append`
 (serialize_asn1_TLV_of_type Generalized_Time `serialize` x.notAfter)
)

noextract inline_for_extraction
let len_of_x509_validity_payload ()
: Tot (asn1_value_int32_of_type SEQUENCE)
= 34ul

val lemma_x509_validity_payload_size
  (x: x509_validity_payload_t)
: Lemma (
  length_of_opaque_serialization serialize_x509_validity_payload x ==
  length_of_opaque_serialization (serialize_asn1_TLV_of_type Generalized_Time) x.notBefore +
  length_of_opaque_serialization (serialize_asn1_TLV_of_type Generalized_Time) x.notAfter /\
  length_of_opaque_serialization serialize_x509_validity_payload x ==
  (v (len_of_x509_validity_payload ()))
)


let x509_validity_t: Type
= inbound_sequence_value_of serialize_x509_validity_payload

noextract
val parse_x509_validity
: parser (parse_asn1_envelop_tag_with_TLV_kind SEQUENCE) (x509_validity_t)

noextract
val serialize_x509_validity
: serializer (parse_x509_validity)

val lemma_serialize_x509_validity_unfold
  (x: x509_validity_t)
: Lemma ( predicate_serialize_asn1_sequence_TLV_unfold serialize_x509_validity_payload x )

val lemma_serialize_x509_validity_size
  (x: x509_validity_t)
: Lemma ( predicate_serialize_asn1_sequence_TLV_size serialize_x509_validity_payload x )

let len_of_x509_validity ()
: Tot (asn1_TLV_int32_of_type SEQUENCE)
= 36ul

val lemma_serialize_x509_validity_size_exact
  (x: x509_validity_t)
: Lemma (
  length_of_opaque_serialization serialize_x509_validity x ==
  (v (len_of_x509_validity ()))
)

noextract inline_for_extraction
val serialize32_x509_validity_payload_backwards
: serializer32_backwards (serialize_x509_validity_payload)

noextract inline_for_extraction
val serialize32_x509_validity_backwards
: serializer32_backwards (serialize_x509_validity)

let x509_get_validity
  (notBefore: datatype_of_asn1_type Generalized_Time)
  (notAfter : datatype_of_asn1_type Generalized_Time)
: Tot (x509_validity_t)
=
  let validity: x509_validity_payload_t = {
      notBefore = notBefore;
      notAfter  = notAfter
  } in

(* return *) validity
