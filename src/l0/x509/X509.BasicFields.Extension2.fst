module X509.BasicFields.Extension2

open LowParse.Spec.Base
open LowParse.Spec.Combinators

open ASN1.Base
open ASN1.Spec
open ASN1.Low

open X509.Base

open FStar.Integers

module B32 = FStar.Bytes

#set-options "--z3rlimit 32 --fuel 0 --ifuel 0"

let parse_x509_extension_payload #k #t #p oid s
=
  parse_asn1_oid_TLV_of oid
  `nondep_then`
  parse_asn1_TLV_of_type BOOLEAN
  `nondep_then`
 (OCTET_STRING
  `parse_asn1_envelop_tag_with_TLV`
  s)

let serialize_x509_extension_payload #k #t #p oid s
= (serialize_asn1_oid_TLV_of oid
   `serialize_nondep_then`
   serialize_asn1_TLV_of_type BOOLEAN
   `serialize_nondep_then`
  (OCTET_STRING
   `serialize_asn1_envelop_tag_with_TLV`
   s))

let lemma_serialize_x509_extension_payload_unfold #k #t #p oid s x
= serialize_nondep_then_eq
  (* s1 *) (serialize_asn1_oid_TLV_of oid)
  (* s2 *) (serialize_asn1_TLV_of_type BOOLEAN)
  (* in *) (fst x);
  serialize_nondep_then_eq
  (* s1 *) (serialize_asn1_oid_TLV_of oid
            `serialize_nondep_then`
            serialize_asn1_TLV_of_type BOOLEAN)
  (* s2 *) (OCTET_STRING
            `serialize_asn1_envelop_tag_with_TLV`
            s)
  (* in *) (x)

let lemma_serialize_x509_extension_payload_size #k #t #p oid s x
= lemma_serialize_x509_extension_payload_unfold oid s x;
  lemma_serialize_asn1_oid_TLV_of_size oid (fst (fst x));
  lemma_serialize_asn1_envelop_tag_with_TLV_size
    OCTET_STRING
    s
    (snd x);
  lemma_serialize_asn1_boolean_TLV_size (snd (fst x))

(*
 * X.509 Extension Combinators
 *)

let parse_x509_extension #k #t #p oid s
= x509_extension_t oid s
  `coerce_parser`
  parse_asn1_sequence_TLV
  (* s *) (serialize_x509_extension_payload oid s)

let serialize_x509_extension #k #t #p oid s
= coerce_parser_serializer
    (parse_x509_extension oid s)
    (serialize_asn1_sequence_TLV
    (* s *) (serialize_x509_extension_payload oid s))
    ()

/// Helpers
///

let lemma_serialize_x509_extension_unfold #k #t #p oid s x
= lemma_serialize_asn1_sequence_TLV_unfold
  (* s *) (serialize_x509_extension_payload oid s)
  x

let lemma_serialize_x509_extension_size #k #t #p oid s x
= lemma_serialize_asn1_sequence_TLV_size
  (* s *) (serialize_x509_extension_payload oid s)
  x

let lemma_serialize_x509_extension_size_exact #k #t #p oid s x x_length
= lemma_serialize_x509_extension_size oid s x;
  lemma_serialize_x509_extension_payload_size oid s x

let serialize32_x509_extension_payload_backwards #k #t #p #s oid s32
= (serialize32_asn1_oid_TLV_of_backwards oid
   `serialize32_nondep_then_backwards`
   serialize32_asn1_TLV_backwards_of_type BOOLEAN
   `serialize32_nondep_then_backwards`
  (OCTET_STRING
   `serialize32_asn1_envelop_tag_with_TLV_backwards`
   s32))

let serialize32_x509_extension_backwards #k #t #p #s oid s32
= coerce_serializer32_backwards
    (serialize_x509_extension oid s)
    (serialize32_asn1_sequence_TLV_backwards
    (* s32 *) (serialize32_x509_extension_payload_backwards oid s32))
    ()
