module X509.Extension

open LowParse.Spec.Base
open LowParse.Spec.Combinators

open ASN1.Base
open ASN1.Spec

open X509.Base

module B32 = FStar.Bytes

noeq
type x509_extension_t
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
= { x509_extID      : datatype_of_asn1_type OID;
    x509_extCritical: datatype_of_asn1_type BOOLEAN;
    x509_extValue   : OCTET_STRING `inbound_envelop_tag_with_value_of` s }

/// tuple repr
let x509_extension_t'
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
= datatype_of_asn1_type OID
  `tuple2`
  datatype_of_asn1_type BOOLEAN
  `tuple2`
 (OCTET_STRING `inbound_envelop_tag_with_value_of` s)

let synth_x509_extension_t
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (x': x509_extension_t' s)
: GTot (x509_extension_t s)
= { x509_extID       = fst (fst x');
    x509_extCritical = snd (fst x');
    x509_extValue    = snd x' }

let synth_x509_extension_t'
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (x: x509_extension_t s)
: GTot (x': x509_extension_t' s { x == synth_x509_extension_t s x' })
= (x.x509_extID, x.x509_extCritical), x.x509_extValue

let parse_x509_extension
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
: parser _ (x509_extension_t s)
= parse_asn1_TLV_of_type OID
  `nondep_then`
  parse_asn1_TLV_of_type BOOLEAN
  `nondep_then`
 (OCTET_STRING
  `parse_asn1_envelop_tag_with_TLV`
  s)
  `parse_synth`
  synth_x509_extension_t s

let serialize_x509_extension
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
: serializer (parse_x509_extension s)
= serialize_synth
  (* p1 *) (parse_asn1_TLV_of_type OID
            `nondep_then`
            parse_asn1_TLV_of_type BOOLEAN
            `nondep_then`
           (OCTET_STRING
            `parse_asn1_envelop_tag_with_TLV`
            s))
  (* f2 *) (synth_x509_extension_t s)
  (* s1 *) (serialize_asn1_TLV_of_type OID
            `serialize_nondep_then`
            serialize_asn1_TLV_of_type BOOLEAN
            `serialize_nondep_then`
           (OCTET_STRING
            `serialize_asn1_envelop_tag_with_TLV`
            s))
  (* g1 *) (synth_x509_extension_t' s)
  (* prf*) ()

let lemma_serialize_x509_extension_unfold
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (x: x509_extension_t s)
: Lemma (
  serialize (serialize_x509_extension s) x ==
  serialize (serialize_asn1_TLV_of_type OID) x.x509_extID
  `Seq.append`
  serialize (serialize_asn1_TLV_of_type BOOLEAN) x.x509_extCritical
  `Seq.append`
  serialize (OCTET_STRING `serialize_asn1_envelop_tag_with_TLV` s) x.x509_extValue
)
= serialize_nondep_then_eq
  (* s1 *) (serialize_asn1_TLV_of_type OID)
  (* s2 *) (serialize_asn1_TLV_of_type BOOLEAN)
  (* in *) (fst (synth_x509_extension_t' s x));
  serialize_nondep_then_eq
  (* s1 *) (serialize_asn1_TLV_of_type OID
            `serialize_nondep_then`
            serialize_asn1_TLV_of_type BOOLEAN)
  (* s2 *) (OCTET_STRING
            `serialize_asn1_envelop_tag_with_TLV`
            s)
  (* in *) (synth_x509_extension_t' s x);
  serialize_synth_eq
  (* p1 *) (parse_asn1_TLV_of_type OID
            `nondep_then`
            parse_asn1_TLV_of_type BOOLEAN
            `nondep_then`
           (OCTET_STRING
            `parse_asn1_envelop_tag_with_TLV`
            s))
  (* f2 *) (synth_x509_extension_t s)
  (* s1 *) (serialize_asn1_TLV_of_type OID
            `serialize_nondep_then`
            serialize_asn1_TLV_of_type BOOLEAN
            `serialize_nondep_then`
           (OCTET_STRING
            `serialize_asn1_envelop_tag_with_TLV`
            s))
  (* g1 *) (synth_x509_extension_t' s)
  (* prf*) ()
  (* in *) x

let lemma_serialize_x509_extension_size
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (x: x509_extension_t s)
: Lemma (
  Seq.length (serialize (serialize_x509_extension s) x) ==
  length_of_asn1_primitive_TLV x.x509_extID +
  length_of_asn1_primitive_TLV x.x509_extCritical +
  Seq.length (serialize (OCTET_STRING `serialize_asn1_envelop_tag_with_TLV` s) x.x509_extValue)
)
= lemma_serialize_x509_extension_unfold s x

unfold
let x509_extension_t_inbound
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
= inbound_sequence_value_of s

/// SEQUENCE TLV

unfold
let parse_x509_extension_sequence_TLV
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
= parse_asn1_sequence_TLV
  (* s *) (serialize_x509_extension s)

unfold
let serialize_x509_extension_sequence_TLV
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
: serializer (parse_x509_extension_sequence_TLV s)
= serialize_asn1_sequence_TLV
  (* s *) (serialize_x509_extension s)

unfold
let lemma_serialize_x509_extension_sequence_TLV_unfold
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
= lemma_serialize_asn1_sequence_TLV_unfold
  (* s *) (serialize_x509_extension s)

unfold
let lemma_serialize_x509_extension_sequence_TLV_size
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
= lemma_serialize_asn1_sequence_TLV_size
  (* s *) (serialize_x509_extension s)

open ASN1.Low

let synth_x509_extension_t'_impl
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (x: x509_extension_t s)
: Tot (x': x509_extension_t' s { x' == synth_x509_extension_t' s x })
= (x.x509_extID, x.x509_extCritical), x.x509_extValue

let serialize32_x509_extension_backwards
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (#s: serializer p)
  (s32: serializer32_backwards s)
: serializer32_backwards (serialize_x509_extension s)
= serialize32_synth_backwards
  (* s32*) (serialize32_asn1_TLV_backwards_of_type OID
            `serialize32_nondep_then_backwards`
            serialize32_asn1_TLV_backwards_of_type BOOLEAN
            `serialize32_nondep_then_backwards`
           (OCTET_STRING
            `serialize32_asn1_envelop_tag_with_TLV_backwards`
            s32))
  (* f2 *) (synth_x509_extension_t s)
  (* g1 *) (synth_x509_extension_t' s)
  (* g1'*) (synth_x509_extension_t'_impl s)
  (* prf*) ()

let serialize32_x509_extension_sequence_TLV_backwards
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (#s: serializer p)
  (s32: serializer32_backwards s)
: serializer32_backwards (serialize_x509_extension_sequence_TLV s)
= serialize32_asn1_sequence_TLV_backwards
  (* s32 *) (serialize32_x509_extension_backwards s32)
