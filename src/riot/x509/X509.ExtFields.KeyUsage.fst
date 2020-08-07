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

let valid_key_usage
  (i: int_32)
: Type0
= 0l < i /\ (* at least one usage *)
  (i <= 0xFFl \/ i / 0x100l == 0x80l)

let key_usage_t = i: int_32
                     { valid_key_usage i }

let x509_KU_DIGITAL_SIGNATURE :key_usage_t = 0x80l    (* bit 0 *)
let x509_KU_NON_REPUDIATION   :key_usage_t = 0x40l    (* bit 1 *)
let x509_KU_KEY_ENCIPHERMENT  :key_usage_t = 0x20l    (* bit 2 *)
let x509_KU_DATA_ENCIPHERMENT :key_usage_t = 0x10l    (* bit 3 *)
let x509_KU_KEY_AGREEMENT     :key_usage_t = 0x08l    (* bit 4 *)
let x509_KU_KEY_CERT_SIGN     :key_usage_t = 0x04l    (* bit 5 *)
let x509_KU_CRL_SIGN          :key_usage_t = 0x02l    (* bit 6 *)
let x509_KU_ENCIPHER_ONLY     :key_usage_t = 0x01l    (* bit 7 *)
let x509_KU_DECIPHER_ONLY     :key_usage_t = 0x8000l  (* bit 8 *)

(* FIXME: Can we normalize bitwise operators? *)
let lemma_key_usage_close_under_or
  (ku1 ku2: key_usage_t)
: Lemma (
  valid_key_usage (ku1 |^ ku2)
)
= admit()

let op_ku_with
  (ku1 ku2: key_usage_t)
: Tot (ku: key_usage_t
           { ku == (ku1 |^ ku2) })
= [@inline_let]let ku: int_32 = ku1 |^ ku2 in
  lemma_key_usage_close_under_or ku1 ku2;
  ku

let _filter_x509_key_usage_payload
  (bs: datatype_of_asn1_type BIT_STRING)
: GTot bool
= bs.bs_len = 3ul &&
  bs.bs_unused_bits = 7ul &&
  (* NOTE: RFC 5280 4.2.1.3:
   *       When the keyUsage extension appears in a certificate,
   *       at least one of the bits MUST be set to 1. *)
  (B32.index bs.bs_s 1 = 0x80uy ||
   B32.index bs.bs_s 1 = 0x00uy && B32.index bs.bs_s 0 > 0x00uy)

let _synth_x509_key_usage_payload
  (bs: parse_filter_refine _filter_x509_key_usage_payload)
: GTot (key_usage_t)
= cast #(Unsigned W8) #(Signed W32) (B32.index bs.bs_s 0) +
  ((cast #(Unsigned W8) #(Signed W32) (B32.index bs.bs_s 1)) * 0x100l)

let lemma_synth_x509_key_usage_payload_injective'
  (bs1 bs2: parse_filter_refine _filter_x509_key_usage_payload)
: Lemma
  (requires _synth_x509_key_usage_payload bs1 == _synth_x509_key_usage_payload bs2)
  (ensures bs1 == bs2)
= admit ()

let lemma_synth_x509_key_usage_injective ()
: Lemma (
  synth_injective _synth_x509_key_usage_payload
)
= synth_injective_intro'
  (* f *) _synth_x509_key_usage_payload
  (*prf*) lemma_synth_x509_key_usage_payload_injective'

let _synth_x509_key_usage_payload_inverse
  (ku: key_usage_t)
: GTot (bs: parse_filter_refine _filter_x509_key_usage_payload
            { _synth_x509_key_usage_payload bs == ku })
= let b0: byte = cast (ku % 0x100l) in
  let b1: byte = cast (ku / 0x100l) in
  let s = Seq.createL [b0; b1] in
  let s32 = B32.hide s in
  { bs_len         = 3ul;
    bs_unused_bits = 7ul;
    bs_s           = s32 }

let _parse_x509_key_usage_payload
: parser _ key_usage_t
= lemma_synth_x509_key_usage_injective ();
  parse_asn1_TLV_of_type BIT_STRING
  `parse_filter`
  _filter_x509_key_usage_payload
  `parse_synth`
  _synth_x509_key_usage_payload

let _serialize_x509_key_usage_payload
: serializer _parse_x509_key_usage_payload
= serialize_synth
  (* p1 *) (parse_asn1_TLV_of_type BIT_STRING
            `parse_filter`
            _filter_x509_key_usage_payload)
  (* f2 *) (_synth_x509_key_usage_payload)
  (* s1 *) (serialize_asn1_TLV_of_type BIT_STRING
            `serialize_filter`
            _filter_x509_key_usage_payload)
  (* g1 *) (_synth_x509_key_usage_payload_inverse)
  (* Prf*) (lemma_synth_x509_key_usage_injective ())

let lemma_serialize_x509_key_usage_payload_unfold
  (ku: key_usage_t)
: Lemma (
  serialize _serialize_x509_key_usage_payload ku ==
  serialize (serialize_asn1_TLV_of_type BIT_STRING) (_synth_x509_key_usage_payload_inverse ku)
)
= serialize_synth_eq
  (* p1 *) (parse_asn1_TLV_of_type BIT_STRING
            `parse_filter`
            _filter_x509_key_usage_payload)
  (* f2 *) (_synth_x509_key_usage_payload)
  (* s1 *) (serialize_asn1_TLV_of_type BIT_STRING
            `serialize_filter`
            _filter_x509_key_usage_payload)
  (* g1 *) (_synth_x509_key_usage_payload_inverse)
  (* Prf*) (lemma_synth_x509_key_usage_injective ())
  (* in *) (ku)

let lemma_serialize_x509_key_usage_payload_size
  (ku: key_usage_t)
: Lemma (
  length_of_opaque_serialization _serialize_x509_key_usage_payload ku ==
  length_of_asn1_primitive_TLV #BIT_STRING (_synth_x509_key_usage_payload_inverse ku)
)
= lemma_serialize_x509_key_usage_payload_unfold ku

(* Complete X509 Key Usage Parser and Serializer for
 *
 *  SEQUENCE {
 *    extID   : OID
 *    extValue: OCTET_STRING {
 *      key_usage    : key_usage_t
 *    }
 *  }
 *
 *)

let key_usage_t_inbound
= inbound_sequence_value_of
    (OID_KEY_USAGE
     `serialize_envelop_OID_with`
    (OCTET_STRING
     `serialize_asn1_envelop_tag_with_TLV`
     _serialize_x509_key_usage_payload))

let parse_x509_key_usage
: parser (parse_asn1_envelop_tag_with_TLV_kind SEQUENCE) key_usage_t_inbound
= key_usage_t_inbound
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

let lemma_serialize_x509_key_usage_unfold
  (x: key_usage_t_inbound)
: Lemma ( predicate_serialize_asn1_sequence_TLV_unfold
            (OID_KEY_USAGE
             `serialize_envelop_OID_with`
            (OCTET_STRING
             `serialize_asn1_envelop_tag_with_TLV`
             _serialize_x509_key_usage_payload))
            x )
= lemma_serialize_asn1_sequence_TLV_unfold
    (OID_KEY_USAGE
     `serialize_envelop_OID_with`
    (OCTET_STRING
             `serialize_asn1_envelop_tag_with_TLV`
             _serialize_x509_key_usage_payload))
    x

let lemma_serialize_x509_key_usage_size
  (x: key_usage_t_inbound)
: Lemma ( predicate_serialize_asn1_sequence_TLV_size
            (OID_KEY_USAGE
             `serialize_envelop_OID_with`
            (OCTET_STRING
             `serialize_asn1_envelop_tag_with_TLV`
             _serialize_x509_key_usage_payload))
            x )
= lemma_serialize_asn1_sequence_TLV_size
    (OID_KEY_USAGE
     `serialize_envelop_OID_with`
    (OCTET_STRING
             `serialize_asn1_envelop_tag_with_TLV`
             _serialize_x509_key_usage_payload))
    x

let length_of_x509_key_usage
  (ku: key_usage_t)
: GTot (asn1_TLV_length_of_type SEQUENCE)
= length_of_TLV
    SEQUENCE
    ( length_of_asn1_primitive_TLV #BIT_STRING (_synth_x509_key_usage_payload_inverse ku) +
      ( length_of_TLV
          OCTET_STRING
          ( length_of_asn1_primitive_TLV #OID OID_KEY_USAGE ) ) )

#restart-solver
#push-options "--z3rlimit 64 --fuel 0 --fuel 0"
let lemma_serialize_x509_key_usage_size_exact
  (x: key_usage_t_inbound)
: Lemma (
  length_of_opaque_serialization serialize_x509_key_usage x
  == length_of_x509_key_usage (snd x)
)
= lemma_serialize_x509_key_usage_size x;
  (**) lemma_serialize_envelop_OID_with_size
         (fst x)
         (OCTET_STRING
          `serialize_asn1_envelop_tag_with_TLV`
          _serialize_x509_key_usage_payload)
         x;
       (**) lemma_serialize_asn1_oid_TLV_of_size (fst x) (fst x);
       (**) lemma_serialize_asn1_envelop_tag_with_TLV_size
              (OCTET_STRING)
              (_serialize_x509_key_usage_payload)
              (snd x);
            (**) lemma_serialize_x509_key_usage_payload_size (snd x)
#pop-options

open ASN1.Low

#push-options "--z3rlimit 32"
let _synth_x509_key_usage_payload_inverse_impl
  (ku: key_usage_t)
: Tot (bs: parse_filter_refine _filter_x509_key_usage_payload
           { bs == _synth_x509_key_usage_payload_inverse ku })
= let b0: byte = FStar.Int.Cast.int32_to_uint8 (ku % 0x100l) in
  let b1: byte = FStar.Int.Cast.int32_to_uint8 (ku / 0x100l) in
  let s32 = B32.(create 1ul b0 `append` create 1ul b1) in
  (* Prf *) B32.extensionality s32 (B32.hide (Seq.createL [b0; b1]));
  { bs_len         = 3ul;
    bs_unused_bits = 7ul;
    bs_s           = s32 }
#pop-options

#push-options "--z3rlimit 32 --fuel 0 --fuel 0"
let len_of_x509_key_usage
  (ku: key_usage_t)
: Tot (len: asn1_TLV_int32_of_type SEQUENCE
            { v len == length_of_x509_key_usage ku })
= len_of_TLV
    SEQUENCE
    ( len_of_asn1_primitive_TLV #BIT_STRING (_synth_x509_key_usage_payload_inverse_impl ku) +
      ( len_of_TLV
          OCTET_STRING
          ( len_of_asn1_primitive_TLV #OID OID_KEY_USAGE ) ) )
#pop-options

let _serialize32_x509_key_usage_payload_backwards
: serializer32_backwards (_serialize_x509_key_usage_payload)
= serialize32_synth_backwards
  (* s1 *) (serialize32_asn1_TLV_backwards_of_type BIT_STRING
            `serialize32_filter_backwards`
            _filter_x509_key_usage_payload)
  (* f2 *) (_synth_x509_key_usage_payload)
  (* g1 *) (_synth_x509_key_usage_payload_inverse)
  (* g1'*) (_synth_x509_key_usage_payload_inverse_impl)
  (* prf*) (lemma_synth_x509_key_usage_injective ())

let serialize32_x509_key_usage_backwards
: serializer32_backwards (serialize_x509_key_usage)
= lemma_synth_x509_key_usage_injective ();
  coerce_serializer32_backwards
  (* s2  *) (serialize_x509_key_usage)
  (* s32 *) (serialize32_asn1_sequence_TLV_backwards
              (OID_KEY_USAGE
               `serialize32_envelop_OID_with_backwards`
              (OCTET_STRING
               `serialize32_asn1_envelop_tag_with_TLV_backwards`
               _serialize32_x509_key_usage_payload_backwards)))
  (* prf *) ()

///
///
/// Helper constructor
#push-options "--z3rlimit 32 --fuel 0 --fuel 0"
let x509_get_key_usage
  (ku: key_usage_t)
// : Tot (key_usage_t_inbound)
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

(*return*) x <: key_usage_t_inbound
#pop-options
