module X509.ExtFields.KeyUsage

open LowParse.Spec.Base
open LowParse.Spec.Combinators

open ASN1.Base
open ASN1.Spec
open ASN1.Low

open X509.Base

module B32 = FStar.Bytes

open FStar.Integers

(*
 * /*
 *  * X.509 v3 Key Usage Extension flags
 *  * Reminder: update x509_info_key_usage() when adding new flags.
 *  */
 * #define MBEDTLS_X509_KU_DIGITAL_SIGNATURE            (0x80)  /* bit 0 */
 * #define MBEDTLS_X509_KU_NON_REPUDIATION              (0x40)  /* bit 1 */
 * #define MBEDTLS_X509_KU_KEY_ENCIPHERMENT             (0x20)  /* bit 2 */
 * #define MBEDTLS_X509_KU_DATA_ENCIPHERMENT            (0x10)  /* bit 3 */
 * #define MBEDTLS_X509_KU_KEY_AGREEMENT                (0x08)  /* bit 4 */
 * #define MBEDTLS_X509_KU_KEY_CERT_SIGN                (0x04)  /* bit 5 */
 * #define MBEDTLS_X509_KU_CRL_SIGN                     (0x02)  /* bit 6 */
 * #define MBEDTLS_X509_KU_ENCIPHER_ONLY                (0x01)  /* bit 7 */
 * #define MBEDTLS_X509_KU_DECIPHER_ONLY              (0x8000)  /* bit 8 */
 *)

#set-options "--fuel 0 --ifuel 0"

let valid_key_usage
  (i: int_32)
: Type0
= 0l < i /\ (* at least one usage *)
  (i <= 0xFFl \/ i / 0x100l == 0x80l)

let key_usage_payload_t = i: int_32
                     { valid_key_usage i }

val x509_KU_DIGITAL_SIGNATURE :key_usage_payload_t // = 0x80l    (* bit 0 *)
val x509_KU_NON_REPUDIATION   :key_usage_payload_t // = 0x40l    (* bit 1 *)
val x509_KU_KEY_ENCIPHERMENT  :key_usage_payload_t // = 0x20l    (* bit 2 *)
val x509_KU_DATA_ENCIPHERMENT :key_usage_payload_t // = 0x10l    (* bit 3 *)
val x509_KU_KEY_AGREEMENT     :key_usage_payload_t // = 0x08l    (* bit 4 *)
val x509_KU_KEY_CERT_SIGN     :key_usage_payload_t // = 0x04l    (* bit 5 *)
val x509_KU_CRL_SIGN          :key_usage_payload_t // = 0x02l    (* bit 6 *)
val x509_KU_ENCIPHER_ONLY     :key_usage_payload_t // = 0x01l    (* bit 7 *)
val x509_KU_DECIPHER_ONLY     :key_usage_payload_t // = 0x8000l  (* bit 8 *)

val lemma_key_usage_close_under_or
  (ku1 ku2: key_usage_payload_t)
: Lemma (
  valid_key_usage (ku1 |^ ku2)
)

val op_ku_with
  (ku1 ku2: key_usage_payload_t)
: Tot (ku: key_usage_payload_t
           { ku == (ku1 |^ ku2) })

let _parse_x509_key_usage_payload_kind
: parser_kind
= parse_filter_kind (parse_asn1_TLV_kind_of_type BIT_STRING)

val _parse_x509_key_usage_payload
: parser _parse_x509_key_usage_payload_kind key_usage_payload_t

val _serialize_x509_key_usage_payload
: serializer _parse_x509_key_usage_payload

// NOTE: Drop the support for reasoning about actual byte content for now
// val lemma_serialize_x509_key_usage_payload_unfold
//   (ku: key_usage_payload_t)
// : Lemma (
//   serialize _serialize_x509_key_usage_payload ku ==
//   serialize (serialize_asn1_TLV_of_type BIT_STRING) (_synth_x509_key_usage_payload_inverse ku)
// )

let length_of_x509_key_usage_payload ()
: GTot (nat)
= 5

let len_of_x509_key_usage_payload ()
: Tot (len: asn1_value_int32_of_type SEQUENCE
            { v len == length_of_x509_key_usage_payload () })
= 5ul

val lemma_serialize_x509_key_usage_payload_size
  (ku: key_usage_payload_t)
: Lemma (
  length_of_opaque_serialization _serialize_x509_key_usage_payload ku ==
  length_of_x509_key_usage_payload ()
)

(* Complete X509 Key Usage Parser and Serializer for
 *
 *  SEQUENCE {
 *    extID   : OID
 *    extValue: OCTET_STRING {
 *      key_usage    : key_usage_payload_t
 *    }
 *  }
 *
 *)

let key_usage_t
= inbound_sequence_value_of
    (OID_KEY_USAGE
     `serialize_envelop_OID_with`
    (OCTET_STRING
     `serialize_asn1_envelop_tag_with_TLV`
     _serialize_x509_key_usage_payload))

let parse_x509_key_usage
: parser (parse_asn1_envelop_tag_with_TLV_kind SEQUENCE) key_usage_t
= key_usage_t
  `coerce_parser`
 (parse_asn1_sequence_TLV
    (OID_KEY_USAGE
     `serialize_envelop_OID_with`
    (OCTET_STRING
     `serialize_asn1_envelop_tag_with_TLV`
     _serialize_x509_key_usage_payload)))

let serialize_x509_key_usage
: serializer (parse_x509_key_usage)
= coerce_parser_serializer
  (* p *) (parse_x509_key_usage)
  (* s *) (serialize_asn1_sequence_TLV
            (OID_KEY_USAGE
             `serialize_envelop_OID_with`
            (OCTET_STRING
             `serialize_asn1_envelop_tag_with_TLV`
             _serialize_x509_key_usage_payload)))
  (*prf*) ()

val lemma_serialize_x509_key_usage_unfold
  (x: key_usage_t)
: Lemma ( predicate_serialize_asn1_sequence_TLV_unfold
            (OID_KEY_USAGE
             `serialize_envelop_OID_with`
            (OCTET_STRING
             `serialize_asn1_envelop_tag_with_TLV`
             _serialize_x509_key_usage_payload))
            x )

val lemma_serialize_x509_key_usage_size
  (x: key_usage_t)
: Lemma ( predicate_serialize_asn1_sequence_TLV_size
            (OID_KEY_USAGE
             `serialize_envelop_OID_with`
            (OCTET_STRING
             `serialize_asn1_envelop_tag_with_TLV`
             _serialize_x509_key_usage_payload))
            x )

let len_of_x509_key_usage ()
: Tot (asn1_TLV_int32_of_type SEQUENCE)
// = len_of_TLV
//     SEQUENCE
//     ( len_of_x509_key_usage_payload () +
//       ( len_of_TLV
//           OCTET_STRING
//           ( len_of_asn1_primitive_TLV #OID OID_KEY_USAGE ) ) )
= 14ul

val lemma_serialize_x509_key_usage_size_exact
  (x: key_usage_t)
: Lemma (
  length_of_opaque_serialization serialize_x509_key_usage x
  == v (len_of_x509_key_usage ())
)

open ASN1.Low

val _serialize32_x509_key_usage_payload_backwards
: serializer32_backwards (_serialize_x509_key_usage_payload)

#set-options "--print_implicits"
val serialize32_x509_key_usage_backwards
: serializer32_backwards (serialize_x509_key_usage)

/// Helper constructor
let x509_get_key_usage
  (ku: key_usage_payload_t)
: Tot (key_usage_t)
=
  (* Prf *) lemma_serialize_x509_key_usage_payload_size ku;
  let x: OID_KEY_USAGE
         `envelop_OID_with_t`
        (OCTET_STRING
         `inbound_envelop_tag_with_value_of`
         _serialize_x509_key_usage_payload)
    = ( OID_KEY_USAGE, ku ) in

  (* Prf *) lemma_serialize_envelop_OID_with_size
              (fst x)
              (OCTET_STRING
               `serialize_asn1_envelop_tag_with_TLV`
               _serialize_x509_key_usage_payload)
              (x);
  (* Prf *) (**) lemma_serialize_asn1_oid_TLV_of_size (fst x) (fst x);
  (* Prf *) (**) lemma_serialize_asn1_envelop_tag_with_TLV_size
                   (OCTET_STRING)
                   (_serialize_x509_key_usage_payload)
                   (snd x);
  (* Prf *)      (**) lemma_serialize_x509_key_usage_payload_size (snd x);

(*return*) x <: key_usage_t
