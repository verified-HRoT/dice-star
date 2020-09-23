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

(* one extension *)
/// tuple repr
noextract inline_for_extraction
let x509_extension_payload_t
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (oid: datatype_of_asn1_type OID)
  (s: Ghost.erased (serializer p))
= parse_filter_refine (filter_asn1_oid_TLV_of oid)
  `tuple2`
  datatype_of_asn1_type BOOLEAN
  `tuple2`
 (OCTET_STRING `inbound_envelop_tag_with_value_of` s)

noextract inline_for_extraction
let x509_get_extension_extValue
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (#oid: datatype_of_asn1_type OID)
  (#s: serializer p)
  (ext: x509_extension_payload_t oid s)
: Tot (t)
= snd ext

let parse_x509_extension_payload_kind
= parse_asn1_TLV_kind_of_type OID
  `and_then_kind`
  parse_asn1_TLV_kind_of_type BOOLEAN
  `and_then_kind`
  parse_asn1_envelop_tag_with_TLV_kind OCTET_STRING

let parse_x509_extension_payload
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (oid: datatype_of_asn1_type OID)
  (s: serializer p)
: parser parse_x509_extension_payload_kind (x509_extension_payload_t oid s)
=
  parse_asn1_oid_TLV_of oid
  `nondep_then`
  parse_asn1_TLV_of_type BOOLEAN
  `nondep_then`
 (OCTET_STRING
  `parse_asn1_envelop_tag_with_TLV`
  s)

let serialize_x509_extension_payload
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (oid: datatype_of_asn1_type OID)
  (s: serializer p)
: serializer (parse_x509_extension_payload oid s)
= (serialize_asn1_oid_TLV_of oid
   `serialize_nondep_then`
   serialize_asn1_TLV_of_type BOOLEAN
   `serialize_nondep_then`
  (OCTET_STRING
   `serialize_asn1_envelop_tag_with_TLV`
   s))

let lemma_serialize_x509_extension_payload_unfold
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (oid: datatype_of_asn1_type OID)
  (s: serializer p)
  (x: x509_extension_payload_t oid s)
: Lemma (
  serialize (serialize_x509_extension_payload oid s) x ==
  serialize (serialize_asn1_oid_TLV_of oid) (fst (fst x))
  `Seq.append`
  serialize (serialize_asn1_TLV_of_type BOOLEAN) (snd (fst x))
  `Seq.append`
  serialize (OCTET_STRING `serialize_asn1_envelop_tag_with_TLV` s) (snd x)
)
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

let length_of_x509_extension_payload_unbounded
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (oid: datatype_of_asn1_type OID)
  (s: serializer p)
  (x: t)
  (x_length: asn1_value_length_of_type OCTET_STRING
             { length_of_opaque_serialization s x == x_length })
: GTot (nat)
= length_of_asn1_primitive_TLV oid +
  length_of_asn1_primitive_TLV true +
  length_of_TLV
    (OCTET_STRING)
    (x_length)

let length_of_x509_extension_payload
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (oid: datatype_of_asn1_type OID)
  (s: serializer p)
  (x: t)
  (x_length: asn1_value_length_of_type OCTET_STRING
             { length_of_opaque_serialization s x == x_length /\
               length_of_x509_extension_payload_unbounded oid s x x_length
               <= asn1_value_length_max_of_type SEQUENCE })
: GTot (asn1_value_length_of_type SEQUENCE)
= length_of_asn1_primitive_TLV oid +
  length_of_asn1_primitive_TLV true +
  length_of_TLV
    (OCTET_STRING)
    (x_length)

noextract inline_for_extraction
let len_of_x509_extension_payload
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (oid: datatype_of_asn1_type OID)
  (s: Ghost.erased (serializer p))
  (x: t)
  (x_len: asn1_value_int32_of_type OCTET_STRING
          { length_of_opaque_serialization s x == v x_len /\
            length_of_x509_extension_payload_unbounded oid s x (v x_len)
            <= asn1_value_length_max_of_type SEQUENCE })
: Tot (len: asn1_value_int32_of_type SEQUENCE
            { v len == length_of_x509_extension_payload oid s x (v x_len) })
= len_of_asn1_primitive_TLV oid +
  len_of_asn1_primitive_TLV true +
  len_of_TLV
    (OCTET_STRING)
    (x_len)

let lemma_serialize_x509_extension_payload_size
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (oid: datatype_of_asn1_type OID)
  (s: serializer p)
  (x: x509_extension_payload_t oid s)
: Lemma (
  length_of_opaque_serialization (serialize_x509_extension_payload oid s) x ==
  length_of_asn1_primitive_TLV #OID     (fst (fst x)) +
  length_of_asn1_primitive_TLV #BOOLEAN (snd (fst x)) +
  length_of_TLV OCTET_STRING (length_of_opaque_serialization s (snd x)) /\
  length_of_asn1_primitive_TLV (snd (fst x)) == 3
)
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

noextract inline_for_extraction
let x509_extension_t
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (oid: datatype_of_asn1_type OID)
  (s: serializer p)
= inbound_sequence_value_of
  (* s *) (serialize_x509_extension_payload  oid s)

let parse_x509_extension_kind
= parse_asn1_envelop_tag_with_TLV_kind SEQUENCE

let parse_x509_extension
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (oid: datatype_of_asn1_type OID)
  (s: serializer p)
: parser parse_x509_extension_kind (x509_extension_t oid s)
= x509_extension_t oid s
  `coerce_parser`
  parse_asn1_sequence_TLV
  (* s *) (serialize_x509_extension_payload oid s)

let serialize_x509_extension
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (oid: datatype_of_asn1_type OID)
  (s: serializer p)
: serializer (parse_x509_extension oid s)
= coerce_parser_serializer
    (parse_x509_extension oid s)
    (serialize_asn1_sequence_TLV
    (* s *) (serialize_x509_extension_payload oid s))
    ()

/// Helpers
///

let predicate_serialize_x509_extension_unfold
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (oid: datatype_of_asn1_type OID)
  (s: serializer p)
  (x: x509_extension_t oid s)
: Type0
= predicate_serialize_asn1_sequence_TLV_unfold (serialize_x509_extension_payload oid s) x

let lemma_serialize_x509_extension_unfold
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (oid: datatype_of_asn1_type OID)
  (s: serializer p)
  (x: x509_extension_t oid s)
: Lemma ( predicate_serialize_x509_extension_unfold oid s x )
= lemma_serialize_asn1_sequence_TLV_unfold
  (* s *) (serialize_x509_extension_payload oid s)
  x

let length_of_x509_extension
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (oid: datatype_of_asn1_type OID)
  (s: serializer p)
  (x: t)
  (x_length: asn1_value_length_of_type OCTET_STRING
             { length_of_opaque_serialization s x == x_length /\
               length_of_x509_extension_payload_unbounded oid s x x_length
               <= asn1_value_length_max_of_type SEQUENCE })
: GTot (asn1_TLV_length_of_type SEQUENCE)
= length_of_TLV
    (SEQUENCE)
    (length_of_x509_extension_payload oid s x x_length)

noextract inline_for_extraction
let len_of_x509_extension
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (oid: datatype_of_asn1_type OID)
  (s: Ghost.erased (serializer p))
  (x: t)
  (x_len: asn1_value_int32_of_type OCTET_STRING
          { length_of_opaque_serialization s x == v x_len /\
            length_of_x509_extension_payload_unbounded oid s x (v x_len)
            <= asn1_value_length_max_of_type SEQUENCE })
: Tot (len: asn1_TLV_int32_of_type SEQUENCE
            { v len == length_of_x509_extension oid s x (v x_len) })
= len_of_TLV
    (SEQUENCE)
    (len_of_x509_extension_payload oid s x x_len)

let predicate_serialize_x509_extension_size
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (oid: datatype_of_asn1_type OID)
  (s: serializer p)
  (x: x509_extension_t oid s)
: Type0
= predicate_serialize_asn1_sequence_TLV_size (serialize_x509_extension_payload oid s) x

let lemma_serialize_x509_extension_size
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (oid: datatype_of_asn1_type OID)
  (s: serializer p)
  (x: x509_extension_t oid s)
: Lemma ( predicate_serialize_x509_extension_size oid s x )
= lemma_serialize_asn1_sequence_TLV_size
  (* s *) (serialize_x509_extension_payload oid s)
  x

let lemma_serialize_x509_extension_size_exact
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (oid: datatype_of_asn1_type OID)
  (s: serializer p)
  (x: x509_extension_t oid s)
  (x_length: asn1_value_length_of_type OCTET_STRING
             { length_of_opaque_serialization s (snd x) == x_length /\
               length_of_x509_extension_payload_unbounded oid s (snd x) x_length
               <= asn1_value_length_max_of_type SEQUENCE })
: Lemma (
  length_of_opaque_serialization (serialize_x509_extension oid s) x ==
  length_of_x509_extension oid s (snd x) x_length
)
= lemma_serialize_x509_extension_size oid s x;
  lemma_serialize_x509_extension_payload_size oid s x

inline_for_extraction noextract
let serialize32_x509_extension_payload_backwards
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (#s: serializer p)
  (oid: datatype_of_asn1_type OID)
  (s32: serializer32_backwards s)
: serializer32_backwards (serialize_x509_extension_payload oid s)
= (serialize32_asn1_oid_TLV_of_backwards oid
   `serialize32_nondep_then_backwards`
   serialize32_asn1_TLV_backwards_of_type BOOLEAN
   `serialize32_nondep_then_backwards`
  (OCTET_STRING
   `serialize32_asn1_envelop_tag_with_TLV_backwards`
   s32))

inline_for_extraction noextract
let serialize32_x509_extension_backwards
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (#s: serializer p)
  (oid: datatype_of_asn1_type OID)
  (s32: serializer32_backwards s)
: serializer32_backwards (serialize_x509_extension oid s)
= coerce_serializer32_backwards
    (serialize_x509_extension oid s)
    (serialize32_asn1_sequence_TLV_backwards
    (* s32 *) (serialize32_x509_extension_payload_backwards oid s32))
    ()

noextract inline_for_extraction
let x509_get_extension
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (oid: datatype_of_asn1_type OID)
  (s: Ghost.erased (serializer p))
  (x: t)
  (x_len: asn1_value_int32_of_type OCTET_STRING
          { length_of_opaque_serialization s x == v x_len /\
            length_of_x509_extension_payload_unbounded oid s x (v x_len)
            <= asn1_value_length_max_of_type SEQUENCE })
  (criticality: datatype_of_asn1_type BOOLEAN)
: Tot (x509_extension_t oid s)
=
  let ext_payload: x509_extension_payload_t oid s = ((oid, criticality), x) in
  lemma_serialize_x509_extension_payload_size oid s ext_payload;

(* return *) ext_payload <: x509_extension_t oid s
