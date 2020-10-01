module X509.BasicFields.Validity

open LowParse.Low.Base

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

#set-options "--z3rlimit 32 --fuel 0 --ifuel 0"

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer
module IB = LowStar.ImmutableBuffer
module B32 = FStar.Bytes

let x509_validity_notAfter_default_buffer
= IB.igcmalloc_of_list HS.root (asn1_generalized_time_for_x509_validity_notAfter_default_list)

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

let parse_x509_validity_payload
= parse_asn1_TLV_of_type Generalized_Time
  `nondep_then`
  parse_asn1_TLV_of_type Generalized_Time
  `parse_synth`
  synth_x509_validity_payload

let serialize_x509_validity_payload
= serialize_synth
  (* p1 *) (parse_asn1_TLV_of_type Generalized_Time
            `nondep_then`
            parse_asn1_TLV_of_type Generalized_Time)
  (* f2 *) (synth_x509_validity_payload)
  (* s1 *) (serialize_asn1_TLV_of_type Generalized_Time
            `serialize_nondep_then`
            serialize_asn1_TLV_of_type Generalized_Time)
  (* g1 *) (synth_x509_validity_payload')
  (* prf*) ()

let lemma_x509_validity_payload_unfold x
= serialize_nondep_then_eq
  (* s1 *) (serialize_asn1_TLV_of_type Generalized_Time)
  (* s2 *) (serialize_asn1_TLV_of_type Generalized_Time)
  (* in *) (synth_x509_validity_payload' x);
  serialize_synth_eq
  (* p1 *) (parse_asn1_TLV_of_type Generalized_Time
            `nondep_then`
            parse_asn1_TLV_of_type Generalized_Time)
  (* f2 *) (synth_x509_validity_payload)
  (* s1 *) (serialize_asn1_TLV_of_type Generalized_Time
            `serialize_nondep_then`
            serialize_asn1_TLV_of_type Generalized_Time)
  (* g1 *) (synth_x509_validity_payload')
  (* prf*) ()
  (* in *) (x)

let lemma_x509_validity_payload_size x
= lemma_x509_validity_payload_unfold x

let lemma_serialize_x509_validity_unfold x
= lemma_serialize_asn1_sequence_TLV_unfold serialize_x509_validity_payload x

let lemma_serialize_x509_validity_size x
= lemma_serialize_asn1_sequence_TLV_size serialize_x509_validity_payload x

let lemma_serialize_x509_validity_size_exact x
= lemma_serialize_x509_validity_size x

let serialize32_x509_validity_payload_backwards
= serialize32_synth_backwards
  (* s32 *) (serialize32_asn1_TLV_backwards_of_type Generalized_Time
             `serialize32_nondep_then_backwards`
             serialize32_asn1_TLV_backwards_of_type Generalized_Time)
  (* f2 *) (synth_x509_validity_payload)
  (* g1 *) (synth_x509_validity_payload')
  (* g1'*) (synth_x509_validity_payload')
  (* prf*) ()

let serialize32_x509_validity_backwards
= coerce_serializer32_backwards
    (serialize_x509_validity)
    (serialize32_asn1_sequence_TLV_backwards
    (**) (serialize32_x509_validity_payload_backwards))
    ()
