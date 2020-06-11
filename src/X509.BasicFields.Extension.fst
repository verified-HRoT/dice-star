module X509.BasicFields.Extension

open LowParse.Spec.Base
open LowParse.Spec.Combinators

open ASN1.Base
open ASN1.Spec

open X509.Base

module B32 = FStar.Bytes

inline_for_extraction
type x509_extension_t
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (oid: datatype_of_asn1_type OID)
  (s: serializer p)
= { x509_extID      : x:datatype_of_asn1_type OID {x == oid};
    x509_extCritical: datatype_of_asn1_type BOOLEAN;
    x509_extValue   : OCTET_STRING `inbound_envelop_tag_with_value_of` s }

/// tuple repr
let x509_extension_t'
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (oid: datatype_of_asn1_type OID)
  (s: serializer p)
= x: datatype_of_asn1_type OID {x == oid}
  `tuple2`
  datatype_of_asn1_type BOOLEAN
  `tuple2`
 (OCTET_STRING `inbound_envelop_tag_with_value_of` s)

let synth_x509_extension_t
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (oid: datatype_of_asn1_type OID)
  (s: serializer p)
  (x': x509_extension_t' oid s)
: GTot (x509_extension_t oid s)
= { x509_extID       = fst (fst x');
    x509_extCritical = snd (fst x');
    x509_extValue    = snd x' }

let synth_x509_extension_t'
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (oid: datatype_of_asn1_type OID)
  (s: serializer p)
  (x: x509_extension_t oid s)
: GTot (x': x509_extension_t' oid s { x == synth_x509_extension_t oid s x' })
= (x.x509_extID, x.x509_extCritical), x.x509_extValue

let parse_x509_extension_kind
= parse_asn1_TLV_kind_of_type OID
  `and_then_kind`
  parse_asn1_TLV_kind_of_type BOOLEAN
  `and_then_kind`
  parse_asn1_envelop_tag_with_TLV_kind OCTET_STRING

let parse_x509_extension
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (oid: datatype_of_asn1_type OID)
  (s: serializer p)
: parser parse_x509_extension_kind (x509_extension_t oid s)
= parse_asn1_oid_TLV_of oid
  `nondep_then`
  parse_asn1_TLV_of_type BOOLEAN
  `nondep_then`
 (OCTET_STRING
  `parse_asn1_envelop_tag_with_TLV`
  s)
  `parse_synth`
  synth_x509_extension_t oid s

let serialize_x509_extension
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (oid: datatype_of_asn1_type OID)
  (s: serializer p)
: serializer (parse_x509_extension oid s)
= serialize_synth
  (* p1 *) (parse_asn1_oid_TLV_of oid
            `nondep_then`
            parse_asn1_TLV_of_type BOOLEAN
            `nondep_then`
           (OCTET_STRING
            `parse_asn1_envelop_tag_with_TLV`
            s))
  (* f2 *) (synth_x509_extension_t oid s)
  (* s1 *) (serialize_asn1_oid_TLV_of oid
            `serialize_nondep_then`
            serialize_asn1_TLV_of_type BOOLEAN
            `serialize_nondep_then`
           (OCTET_STRING
            `serialize_asn1_envelop_tag_with_TLV`
            s))
  (* g1 *) (synth_x509_extension_t' oid s)
  (* prf*) ()

let lemma_serialize_x509_extension_unfold
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (oid: datatype_of_asn1_type OID)
  (s: serializer p)
  (x: x509_extension_t oid s)
: Lemma (
  serialize (serialize_x509_extension oid s) x ==
  serialize (serialize_asn1_oid_TLV_of oid) x.x509_extID
  `Seq.append`
  serialize (serialize_asn1_TLV_of_type BOOLEAN) x.x509_extCritical
  `Seq.append`
  serialize (OCTET_STRING `serialize_asn1_envelop_tag_with_TLV` s) x.x509_extValue
)
= serialize_nondep_then_eq
  (* s1 *) (serialize_asn1_oid_TLV_of oid)
  (* s2 *) (serialize_asn1_TLV_of_type BOOLEAN)
  (* in *) (fst (synth_x509_extension_t' oid s x));
  serialize_nondep_then_eq
  (* s1 *) (serialize_asn1_oid_TLV_of oid
            `serialize_nondep_then`
            serialize_asn1_TLV_of_type BOOLEAN)
  (* s2 *) (OCTET_STRING
            `serialize_asn1_envelop_tag_with_TLV`
            s)
  (* in *) (synth_x509_extension_t' oid s x);
  serialize_synth_eq
  (* p1 *) (parse_asn1_oid_TLV_of oid
            `nondep_then`
            parse_asn1_TLV_of_type BOOLEAN
            `nondep_then`
           (OCTET_STRING
            `parse_asn1_envelop_tag_with_TLV`
            s))
  (* f2 *) (synth_x509_extension_t oid s)
  (* s1 *) (serialize_asn1_oid_TLV_of oid
            `serialize_nondep_then`
            serialize_asn1_TLV_of_type BOOLEAN
            `serialize_nondep_then`
           (OCTET_STRING
            `serialize_asn1_envelop_tag_with_TLV`
            s))
  (* g1 *) (synth_x509_extension_t' oid s)
  (* prf*) ()
  (* in *) x

#push-options "--z3rlimit 32 --fuel 4 --ifuel 4"
let lemma_serialize_x509_extension_size
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (oid: datatype_of_asn1_type OID)
  (s: serializer p)
  (x: x509_extension_t oid s)
: Lemma (
  Seq.length (serialize (serialize_x509_extension oid s) x) ==
  length_of_asn1_primitive_TLV x.x509_extID +
  length_of_asn1_primitive_TLV x.x509_extCritical +
  length_of_TLV OCTET_STRING (length_of_opaque_serialization s x.x509_extValue) /\
  length_of_asn1_primitive_TLV x.x509_extCritical == 3
)
= lemma_serialize_x509_extension_unfold oid s x;
  lemma_serialize_asn1_oid_TLV_of_size oid x.x509_extID;
  lemma_serialize_asn1_envelop_tag_with_TLV_size
    OCTET_STRING
    s
    x.x509_extValue;
  lemma_serialize_asn1_boolean_TLV_size x.x509_extCritical
#pop-options

unfold
let x509_extension_t_inbound
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (oid: datatype_of_asn1_type OID)
  (s: serializer p)
= inbound_sequence_value_of
  (* s *) (serialize_x509_extension oid s)

/// SEQUENCE TLV

let parse_x509_extension_sequence_TLV_kind
= parse_asn1_envelop_tag_with_TLV_kind SEQUENCE

unfold
let parse_x509_extension_sequence_TLV
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (oid: datatype_of_asn1_type OID)
  (s: serializer p)
: parser parse_x509_extension_sequence_TLV_kind (x509_extension_t_inbound oid s)
= parse_asn1_sequence_TLV
  (* s *) (serialize_x509_extension oid s)

unfold
let serialize_x509_extension_sequence_TLV
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (oid: datatype_of_asn1_type OID)
  (s: serializer p)
: serializer (parse_x509_extension_sequence_TLV oid s)
= serialize_asn1_sequence_TLV
  (* s *) (serialize_x509_extension oid s)

unfold
let lemma_serialize_x509_extension_sequence_TLV_unfold
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (oid: datatype_of_asn1_type OID)
  (s: serializer p)
  (x: x509_extension_t_inbound oid s)
: Lemma ( predicate_serialize_asn1_sequence_TLV_unfold (serialize_x509_extension oid s) x )
= lemma_serialize_asn1_sequence_TLV_unfold
  (* s *) (serialize_x509_extension oid s)
  x

unfold
let lemma_serialize_x509_extension_sequence_TLV_size
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (oid: datatype_of_asn1_type OID)
  (s: serializer p)
  (x: x509_extension_t_inbound oid s)
: Lemma ( predicate_serialize_asn1_sequence_TLV_size (serialize_x509_extension oid s) x )
= lemma_serialize_asn1_sequence_TLV_size
  (* s *) (serialize_x509_extension oid s)
  x

open ASN1.Low

inline_for_extraction noextract
let synth_x509_extension_t'_impl
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (oid: datatype_of_asn1_type OID)
  (s: serializer p)
  (x: x509_extension_t oid s)
: Tot (x': x509_extension_t' oid s { x' == synth_x509_extension_t' oid s x })
= (x.x509_extID, x.x509_extCritical), x.x509_extValue


//AR: 06/11: this and the next one seem helpers to me?
inline_for_extraction noextract
let serialize32_x509_extension_backwards
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (#s: serializer p)
  (oid: datatype_of_asn1_type OID)
  (s32: serializer32_backwards s)
: serializer32_backwards (serialize_x509_extension oid s)
= serialize32_synth_backwards
  (* s32*) (serialize32_asn1_oid_TLV_of_backwards oid
            `serialize32_nondep_then_backwards`
            serialize32_asn1_TLV_backwards_of_type BOOLEAN
            `serialize32_nondep_then_backwards`
           (OCTET_STRING
            `serialize32_asn1_envelop_tag_with_TLV_backwards`
            s32))
  (* f2 *) (synth_x509_extension_t oid s)
  (* g1 *) (synth_x509_extension_t' oid s)
  (* g1'*) (synth_x509_extension_t'_impl oid s)
  (* prf*) ()

inline_for_extraction noextract
let serialize32_x509_extension_sequence_TLV_backwards
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (#s: serializer p)
  (oid: datatype_of_asn1_type OID)
  (s32: serializer32_backwards s)
: serializer32_backwards (serialize_x509_extension_sequence_TLV oid s)
= serialize32_asn1_sequence_TLV_backwards
  (* s32 *) (serialize32_x509_extension_backwards oid s32)

let _ = assert (length_of_oid OID_EC_GRP_SECP256R1 == 6)
