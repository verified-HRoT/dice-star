module X509.BasicFields.Extension

open X509.Base

#set-options "--z3rlimit 32 --fuel 0 --ifuel 0"

// inline_for_extraction
// type x509_extension_t
//   (#k: parser_kind)
//   (#t: Type0)
//   (#p: parser k t)
//   (oid: datatype_of_asn1_type OID)
//   (s: serializer p)
// = { x509_extID      : x:datatype_of_asn1_type OID {x == oid};
//     x509_extCritical: datatype_of_asn1_type BOOLEAN;
//     x509_extValue   : OCTET_STRING `inbound_envelop_tag_with_value_of` s }

(* one extension *)

// let synth_x509_extension_t
//   (#k: parser_kind)
//   (#t: Type0)
//   (#p: parser k t)
//   (oid: datatype_of_asn1_type OID)
//   (s: serializer p)
//   (x': x509_extension_t' oid s)
// : GTot (x509_extension_t oid s)
// = { x509_extID       = fst (fst x');
//     x509_extCritical = snd (fst x');
//     x509_extValue    = snd x' }

// let synth_x509_extension_t'
//   (#k: parser_kind)
//   (#t: Type0)
//   (#p: parser k t)
//   (oid: datatype_of_asn1_type OID)
//   (s: serializer p)
//   (x: x509_extension_t oid s)
// : GTot (x': x509_extension_t' oid s { x == synth_x509_extension_t oid s x' })
// = (x.x509_extID, x.x509_extCritical), x.x509_extValue

let parse_x509_extension #k #t #p oid s #instance_t f prf
=
  parse_asn1_oid_TLV_of oid
  `nondep_then`
  parse_asn1_TLV_of_type BOOLEAN
  `nondep_then`
 (OCTET_STRING
  `parse_asn1_envelop_tag_with_TLV`
  s)
  `parse_synth`
  (prf; f)

let serialize_x509_extension #k #t #p oid s #instance_t f g prf
=
  serialize_synth
  (* p1 *) (parse_asn1_oid_TLV_of oid
            `nondep_then`
            parse_asn1_TLV_of_type BOOLEAN
            `nondep_then`
           (OCTET_STRING
            `parse_asn1_envelop_tag_with_TLV`
            s))
  (* f2 *) (f)
  (* s1 *) (serialize_asn1_oid_TLV_of oid
            `serialize_nondep_then`
            serialize_asn1_TLV_of_type BOOLEAN
            `serialize_nondep_then`
           (OCTET_STRING
            `serialize_asn1_envelop_tag_with_TLV`
            s))
  (* g1 *) (g)
  (* prf*) (prf)

let lemma_serialize_x509_extension_unfold #k #t #p oid s #instance_t f g prf x
= serialize_nondep_then_eq
  (* s1 *) (serialize_asn1_oid_TLV_of oid)
  (* s2 *) (serialize_asn1_TLV_of_type BOOLEAN)
  (* in *) (fst (g x));
  serialize_nondep_then_eq
  (* s1 *) (serialize_asn1_oid_TLV_of oid
            `serialize_nondep_then`
            serialize_asn1_TLV_of_type BOOLEAN)
  (* s2 *) (OCTET_STRING
            `serialize_asn1_envelop_tag_with_TLV`
            s)
  (* in *) (g x);
  serialize_synth_eq
  (* p1 *) (parse_asn1_oid_TLV_of oid
            `nondep_then`
            parse_asn1_TLV_of_type BOOLEAN
            `nondep_then`
           (OCTET_STRING
            `parse_asn1_envelop_tag_with_TLV`
            s))
  (* f2 *) (f)
  (* s1 *) (serialize_asn1_oid_TLV_of oid
            `serialize_nondep_then`
            serialize_asn1_TLV_of_type BOOLEAN
            `serialize_nondep_then`
           (OCTET_STRING
            `serialize_asn1_envelop_tag_with_TLV`
            s))
  (* g1 *) (g)
  (* prf*) (prf)
  (* in *) x

#push-options "--z3rlimit 32 --fuel 4 --ifuel 4"
let lemma_serialize_x509_extension_size #k #t #p oid s #instance_t f g prf x
= lemma_serialize_x509_extension_unfold oid s f g prf x;
  lemma_serialize_asn1_oid_TLV_of_size oid (fst (fst (g x)));
  lemma_serialize_asn1_envelop_tag_with_TLV_size
    OCTET_STRING
    s
    (snd (g x));
  lemma_serialize_asn1_boolean_TLV_size (snd (fst (g x)))
#pop-options

let parse_x509_extension_sequence_TLV #k #t #p oid s #instance_t f g prf
= parse_asn1_sequence_TLV
  (* s *) (serialize_x509_extension oid s f g prf)

let serialize_x509_extension_sequence_TLV #k #t #p oid s #instance_t f g prf
= serialize_asn1_sequence_TLV
  (* s *) (serialize_x509_extension oid s f g prf)

let lemma_serialize_x509_extension_sequence_TLV_unfold #k #t #p oid s #instance_t f g prf x
= lemma_serialize_asn1_sequence_TLV_unfold
  (* s *) (serialize_x509_extension oid s f g prf)
  x

let lemma_serialize_x509_extension_sequence_TLV_size #k #t #p oid s #instance_t f g prf x
= lemma_serialize_asn1_sequence_TLV_size
  (* s *) (serialize_x509_extension oid s f g prf)
  x

open ASN1.Low

// inline_for_extraction noextract
// let synth_x509_extension_t'_impl
//   (#k: parser_kind)
//   (#t: Type0)
//   (#p: parser k t)
//   (oid: datatype_of_asn1_type OID)
//   (s: serializer p)
//   (x: x509_extension_t oid s)
// : Tot (x': x509_extension_t' oid s { x' == synth_x509_extension_t' oid s x })
// = (x.x509_extID, x.x509_extCritical), x.x509_extValue

//AR: 06/11: this and the next one seem helpers to me?
let serialize32_x509_extension_backwards #k #t #p #s oid s32 #instance_t f g g' prf
= serialize32_synth_backwards
  (* s32*) (serialize32_asn1_oid_TLV_of_backwards oid
            `serialize32_nondep_then_backwards`
            serialize32_asn1_TLV_backwards_of_type BOOLEAN
            `serialize32_nondep_then_backwards`
           (OCTET_STRING
            `serialize32_asn1_envelop_tag_with_TLV_backwards`
            s32))
  (* f2 *) (f)
  (* g1 *) (g)
  (* g1'*) (g')
  (* prf*) (prf)

let serialize32_x509_extension_sequence_TLV_backwards #k #t #p #s oid s32 #instance_t f g g' prf
= serialize32_asn1_sequence_TLV_backwards
  (* s32 *) (serialize32_x509_extension_backwards oid s32 f g g' prf)
