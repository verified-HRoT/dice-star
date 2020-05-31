module X509.ExtFields.KeyUsage

open LowParse.Spec.Base
open LowParse.Spec.Combinators

open ASN1.Base
open ASN1.Spec

open X509.Base

module B32 = FStar.Bytes

open FStar.Integers

(*
/*
 * X.509 v3 Key Usage Extension flags
 * Reminder: update x509_info_key_usage() when adding new flags.
 */
#define MBEDTLS_X509_KU_DIGITAL_SIGNATURE            (0x80)  /* bit 0 */
#define MBEDTLS_X509_KU_NON_REPUDIATION              (0x40)  /* bit 1 */
#define MBEDTLS_X509_KU_KEY_ENCIPHERMENT             (0x20)  /* bit 2 */
#define MBEDTLS_X509_KU_DATA_ENCIPHERMENT            (0x10)  /* bit 3 */
#define MBEDTLS_X509_KU_KEY_AGREEMENT                (0x08)  /* bit 4 */
#define MBEDTLS_X509_KU_KEY_CERT_SIGN                (0x04)  /* bit 5 */
#define MBEDTLS_X509_KU_CRL_SIGN                     (0x02)  /* bit 6 */
#define MBEDTLS_X509_KU_ENCIPHER_ONLY                (0x01)  /* bit 7 */
#define MBEDTLS_X509_KU_DECIPHER_ONLY              (0x8000)  /* bit 8 */
*)

let key_usage_t = i: datatype_of_asn1_type INTEGER
                     { 0l < i /\ (* at least one usage *)
                      (i <= 0xFFl \/ i / 0x100l == 0x80l) }

let x509_KU_DIGITAL_SIGNATURE :key_usage_t = 0x80l    (* bit 0 *)
let x509_KU_NON_REPUDIATION   :key_usage_t = 0x40l    (* bit 1 *)
let x509_KU_KEY_ENCIPHERMENT  :key_usage_t = 0x20l    (* bit 2 *)
let x509_KU_DATA_ENCIPHERMENT :key_usage_t = 0x10l    (* bit 3 *)
let x509_KU_KEY_AGREEMENT     :key_usage_t = 0x08l    (* bit 4 *)
let x509_KU_KEY_CERT_SIGN     :key_usage_t = 0x04l    (* bit 5 *)
let x509_KU_CRL_SIGN          :key_usage_t = 0x02l    (* bit 6 *)
let x509_KU_ENCIPHER_ONLY     :key_usage_t = 0x01l    (* bit 7 *)
let x509_KU_DECIPHER_ONLY     :key_usage_t = 0x8000l  (* bit 8 *)

let filter_x509_key_usage
  (bs: datatype_of_asn1_type BIT_STRING)
: GTot bool
= bs.bs_len = 3ul &&
  bs.bs_unused_bits = 7ul &&
  (* NOTE: RFC 5280 4.2.1.3:
//            When the keyUsage extension appears in a certificate,
//            at least one of the bits MUST be set to 1.*)
  (B32.index bs.bs_s 1 = 0x80uy ||
   B32.index bs.bs_s 1 = 0x00uy && B32.index bs.bs_s 0 > 0x00uy)

let synth_x509_key_usage
  (bs: parse_filter_refine filter_x509_key_usage)
: GTot (key_usage_t)
= cast #(Unsigned W8) #(Signed W32) (B32.index bs.bs_s 0) +
  ((cast #(Unsigned W8) #(Signed W32) (B32.index bs.bs_s 1)) * 0x100l)

let lemma_synth_x509_key_usage_injective'
  (bs1 bs2: parse_filter_refine filter_x509_key_usage)
: Lemma
  (requires synth_x509_key_usage bs1 == synth_x509_key_usage bs2)
  (ensures bs1 == bs2)
= admit ()

let lemma_synth_x509_key_usage_injective ()
: Lemma (
  synth_injective synth_x509_key_usage
)
= synth_injective_intro'
  (* f *) synth_x509_key_usage
  (*prf*) lemma_synth_x509_key_usage_injective'

let synth_x509_key_usage_inverse
  (ku: key_usage_t)
: GTot (bs: parse_filter_refine filter_x509_key_usage
            { synth_x509_key_usage bs == ku })
= let b0: byte = cast (ku % 0x100l) in
  let b1: byte = cast (ku / 0x100l) in
  let s = Seq.createL [b0; b1] in
  let s32 = B32.hide s in
  { bs_len         = 3ul;
    bs_unused_bits = 7ul;
    bs_s           = s32 }

let parse_x509_key_usage
: parser _ key_usage_t
= lemma_synth_x509_key_usage_injective ();
  parse_asn1_TLV_of_type BIT_STRING
  `parse_filter`
  filter_x509_key_usage
  `parse_synth`
  synth_x509_key_usage

let serialize_x509_key_usage
: serializer parse_x509_key_usage
= serialize_synth
  (* p1 *) (parse_asn1_TLV_of_type BIT_STRING
            `parse_filter`
            filter_x509_key_usage)
  (* f2 *) (synth_x509_key_usage)
  (* s1 *) (serialize_asn1_TLV_of_type BIT_STRING
            `serialize_filter`
            filter_x509_key_usage)
  (* g1 *) (synth_x509_key_usage_inverse)
  (* Prf*) (lemma_synth_x509_key_usage_injective ())

let lemma_serialize_x509_key_usage_unfold
  (ku: key_usage_t)
: Lemma (
  serialize serialize_x509_key_usage ku ==
  serialize (serialize_asn1_TLV_of_type BIT_STRING) (synth_x509_key_usage_inverse ku)
)
= serialize_synth_eq
  (* p1 *) (parse_asn1_TLV_of_type BIT_STRING
            `parse_filter`
            filter_x509_key_usage)
  (* f2 *) (synth_x509_key_usage)
  (* s1 *) (serialize_asn1_TLV_of_type BIT_STRING
            `serialize_filter`
            filter_x509_key_usage)
  (* g1 *) (synth_x509_key_usage_inverse)
  (* Prf*) (lemma_synth_x509_key_usage_injective ())
  (* in *) (ku)

let lemma_serialize_x509_key_usage_size
  (ku: key_usage_t)
: Lemma (
  Seq.length (serialize serialize_x509_key_usage ku) ==
  length_of_asn1_primitive_TLV #BIT_STRING (synth_x509_key_usage_inverse ku)
)
= lemma_serialize_x509_key_usage_unfold ku

// let parse_envelop_OID_with
//   (oid: datatype_of_asn1_type OID)
//   (#k: parser_kind)
//   (#t: Type0)
//   (#p: parser k t)
//   (s: serializer p)
// : parser _ _
// = parse_asn1_oid_TLV
//   `parse_filter`
//   (fun x -> x = oid)
//   `nondep_then`
//   p

let parse_x509_key_usage_sequence_TLV
= parse_asn1_sequence_TLV
    (OID_KEY_USAGE
     `serialize_envelop_OID_with`
     serialize_x509_key_usage)

let serialize_x509_key_usage_sequence_TLV
= serialize_asn1_sequence_TLV
    (OID_KEY_USAGE
     `serialize_envelop_OID_with`
     serialize_x509_key_usage)

let lemma_serialize_x509_key_usage_sequence_TLV_unfold
= lemma_serialize_asn1_sequence_TLV_unfold
    (OID_KEY_USAGE
     `serialize_envelop_OID_with`
     serialize_x509_key_usage)

let lemma_serialize_x509_key_usage_sequence_TLV_size
= lemma_serialize_asn1_sequence_TLV_size
    (OID_KEY_USAGE
     `serialize_envelop_OID_with`
     serialize_x509_key_usage)

open ASN1.Low

let synth_x509_key_usage_inverse_impl
  (ku: key_usage_t)
: Tot (bs: parse_filter_refine filter_x509_key_usage
           { bs == synth_x509_key_usage_inverse ku })
= let b0: byte = cast (ku % 0x100l) in
  let b1: byte = cast (ku / 0x100l) in
  let s32 = B32.(create 1ul b0 `append` create 1ul b1) in
  (* Prf *) B32.extensionality s32 (B32.hide (Seq.createL [b0; b1]));
  { bs_len         = 3ul;
    bs_unused_bits = 7ul;
    bs_s           = s32 }

let serialize32_x509_key_usage_backwards
: serializer32_backwards (serialize_x509_key_usage)
= serialize32_synth_backwards
  (* s1 *) (serialize32_asn1_TLV_backwards_of_type BIT_STRING
            `serialize32_filter_backwards`
            filter_x509_key_usage)
  (* f2 *) (synth_x509_key_usage)
  (* g1 *) (synth_x509_key_usage_inverse)
  (* g1'*) (synth_x509_key_usage_inverse_impl)
  (* prf*) (lemma_synth_x509_key_usage_injective ())

let serialize32_x509_key_usage_sequence_TLV_backwards
: serializer32_backwards (serialize_x509_key_usage_sequence_TLV)
= lemma_synth_x509_key_usage_injective ();
  serialize32_asn1_sequence_TLV_backwards
    (OID_KEY_USAGE
     `serialize32_envelop_OID_with_backwards`
     serialize32_x509_key_usage_backwards)
