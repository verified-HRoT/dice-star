module X509.ExtFields.BasicConstraints

open LowParse.Spec.Base
open LowParse.Spec.Combinators

open ASN1.Base
open ASN1.Spec

open X509.Base

module B32 = FStar.Bytes

open FStar.Integers

(* Not using for now

let x509_basic_constraints_t
  (hasLenField: bool)
= if hasLenField then
  ( tuple2 (datatype_of_asn1_type BOOLEAN) (datatype_of_asn1_type INTEGER) )
  else
  ( bool )

let parse_x509_basic_constraints_kind
  (hasLenField: bool)
: k: parser_kind {Mkparser_kind'?.parser_kind_subkind k == Some ParserStrong}
= if hasLenField then
  ( parse_asn1_TLV_kind_of_type BOOLEAN
    `and_then_kind`
    parse_asn1_TLV_kind_of_type INTEGER )
  else
  ( parse_asn1_TLV_kind_of_type BOOLEAN )

let parse_x509_basic_constraints
  (hasLenField: bool)
: parser (parse_x509_basic_constraints_kind hasLenField) (x509_basic_constraints_t hasLenField)
= if hasLenField then
  ( parse_asn1_TLV_of_type BOOLEAN
    `nondep_then`
    parse_asn1_TLV_of_type INTEGER )
  else
  ( parse_asn1_TLV_of_type BOOLEAN )

let serialize_x509_basic_constraints
  (hasLenField: bool)
: serializer (parse_x509_basic_constraints hasLenField)
= if hasLenField then
  ( serialize_asn1_TLV_of_type BOOLEAN
    `serialize_nondep_then`
    serialize_asn1_TLV_of_type INTEGER )
  else
  ( serialize_asn1_TLV_of_type BOOLEAN )

let lemma_serialize_x509_basic_constraints_unfold
  (hasLenField: bool)
  (x: x509_basic_constraints_t hasLenField)
: Lemma (
  serialize (serialize_x509_basic_constraints hasLenField) x ==
  ( if hasLenField then
    ( let x = x <: datatype_of_asn1_type BOOLEAN `tuple2` datatype_of_asn1_type INTEGER in
      serialize (serialize_asn1_TLV_of_type BOOLEAN) (fst x)
      `Seq.append`
      serialize (serialize_asn1_TLV_of_type INTEGER) (snd x) )
    else
    ( let x = x <: datatype_of_asn1_type BOOLEAN in
      serialize (serialize_asn1_TLV_of_type BOOLEAN) x ) )
)
= if hasLenField then
  ( serialize_nondep_then_eq
    (* s1 *) (serialize_asn1_TLV_of_type BOOLEAN)
    (* s2 *) (serialize_asn1_TLV_of_type INTEGER)
    (* in *) x )
  else
  ( () )

let lemma_serialize_x509_basic_constraints_size
  (hasLenField: bool)
  (x: x509_basic_constraints_t hasLenField)
: Lemma (
  Seq.length (serialize (serialize_x509_basic_constraints hasLenField) x) ==
  ( if hasLenField then
    ( let x = x <: datatype_of_asn1_type BOOLEAN `tuple2` datatype_of_asn1_type INTEGER in
      length_of_asn1_primitive_TLV (fst x) +
      length_of_asn1_primitive_TLV (snd x) )
    else
    ( let x = x <: datatype_of_asn1_type BOOLEAN in
      length_of_asn1_primitive_TLV x ) )
)
= lemma_serialize_x509_basic_constraints_unfold hasLenField x

let parse_x509_basic_constraints_sequence_TLV
  (hasLenField: bool)
= parse_asn1_sequence_TLV
    (OID_BASIC_CONSTRAINTS
     `serialize_envelop_OID_with`
     serialize_x509_basic_constraints hasLenField)

let serialize_x509_basic_constraints_sequence_TLV
  (hasLenField: bool)
: serializer (parse_x509_basic_constraints_sequence_TLV hasLenField)
= serialize_asn1_sequence_TLV
    (OID_BASIC_CONSTRAINTS
     `serialize_envelop_OID_with`
     serialize_x509_basic_constraints hasLenField)

let lemma_serialize_x509_basic_constraints_sequence_TLV_unfold
  (hasLenField: bool)
= lemma_serialize_asn1_sequence_TLV_unfold
    (OID_BASIC_CONSTRAINTS
     `serialize_envelop_OID_with`
     serialize_x509_basic_constraints hasLenField)

let lemma_serialize_x509_basic_constraints_sequence_TLV_size
  (hasLenField: bool)
= lemma_serialize_asn1_sequence_TLV_size
    (OID_BASIC_CONSTRAINTS
     `serialize_envelop_OID_with`
     serialize_x509_basic_constraints hasLenField)

open ASN1.Low

let x509_basic_constraints_t_inbound
  (hasLenField: bool)
= inbound_sequence_value_of (serialize_x509_basic_constraints hasLenField)

noextract
let serialize32_x509_basic_constraints_backwards
  (hasLenField: bool)
: serializer32_backwards (serialize_x509_basic_constraints hasLenField)
= if hasLenField then
  ( serialize32_asn1_TLV_backwards_of_type BOOLEAN
    `serialize32_nondep_then_backwards`
    serialize32_asn1_TLV_backwards_of_type INTEGER )
  else
  ( serialize32_asn1_TLV_backwards_of_type BOOLEAN )

let serialize32_x509_basic_constraints_sequence_TLV_backwards
  (hasLenField: bool)
: serializer32_backwards (serialize_x509_basic_constraints_sequence_TLV hasLenField)
= serialize32_asn1_sequence_TLV_backwards
  (* s32 *) (OID_BASIC_CONSTRAINTS
             `serialize32_envelop_OID_with_backwards`
             serialize32_x509_basic_constraints_backwards hasLenField)

let _ = assert (length_of_oid OID_EC_GRP_SECP256R1 == 6)
