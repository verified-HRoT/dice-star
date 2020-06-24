module X509.ExtFields.ExtendedKeyUsage

open LowParse.Spec.Base
open LowParse.Spec.Combinators

open ASN1.Base
open ASN1.Spec

open X509.Base

module B32 = FStar.Bytes

noextract unfold
let valid_keyPurposeIDs
  (oids: list (datatype_of_asn1_type OID))
= 0 < List.length oids /\
  FStar.Integers.(within_bounds (Unsigned W32) (List.length oids))

let rec x509_ext_key_usage_t
  (oids: list (datatype_of_asn1_type OID) { valid_keyPurposeIDs oids})
: Tot (Type0)
  (decreases (List.length oids))
= let oids', oid = List.Tot.Base.unsnoc oids in
  List.Tot.Properties.lemma_unsnoc_length oids;
  match oids' with
  | [] -> ( get_parser_type (parse_asn1_oid_TLV_of oid) )
  | _  -> ( x509_ext_key_usage_t oids'
            `tuple2`
            get_parser_type (parse_asn1_oid_TLV_of oid) )

let rec get_x509_ext_key_usage
  (oids: list (datatype_of_asn1_type OID) { valid_keyPurposeIDs oids})
: Tot (x509_ext_key_usage_t oids)
  (decreases (List.length oids))
= let oids', oid = List.Tot.Base.unsnoc oids in
  List.Tot.Properties.lemma_unsnoc_length oids;
  match oids' with
  | [] -> ( oid )
  | _  -> ( (get_x509_ext_key_usage oids', oid)
             <: x509_ext_key_usage_t oids'
                `tuple2`
                get_parser_type (parse_asn1_oid_TLV_of oid) )

let rec parse_x509_ext_key_usage_kind
  (oids: list (datatype_of_asn1_type OID) { valid_keyPurposeIDs oids})
: Tot (k: parser_kind { Mkparser_kind'?.parser_kind_subkind k == Some ParserStrong })
  (decreases (List.length oids))
= let oids', oid = List.Tot.Base.unsnoc oids in
  List.Tot.Properties.lemma_unsnoc_length oids;
  match oids' with
  | [] -> ( get_parser_kind (parse_asn1_oid_TLV_of oid) )
  | _  -> ( parse_x509_ext_key_usage_kind oids'
            `and_then_kind`
            get_parser_kind (parse_asn1_oid_TLV_of oid) )

let rec parse_x509_ext_key_usage
  (oids: list (datatype_of_asn1_type OID) {valid_keyPurposeIDs oids})
: Tot (parser (parse_x509_ext_key_usage_kind oids) (x509_ext_key_usage_t oids))
  (decreases (List.length oids))
= let oids', oid = List.Tot.Base.unsnoc oids in
  List.Tot.Properties.lemma_unsnoc_length oids;
  match oids' with
  | [] -> ( parse_asn1_oid_TLV_of oid )
  | _  -> ( parse_x509_ext_key_usage oids'
            `nondep_then`
            parse_asn1_oid_TLV_of oid )

let rec serialize_x509_ext_key_usage
  (oids: list (datatype_of_asn1_type OID) {valid_keyPurposeIDs oids})
: Tot (serializer (parse_x509_ext_key_usage oids))
  (decreases (List.length oids))
= let oids', oid = List.Tot.Base.unsnoc oids in
  List.Tot.Properties.lemma_unsnoc_length oids;
  match oids' with
  | [] -> ( serialize_asn1_oid_TLV_of oid )
  | _  -> ( serialize_x509_ext_key_usage oids'
            `serialize_nondep_then`
            serialize_asn1_oid_TLV_of oid )

let rec serialize_x509_ext_key_usage_unfold_spec
  (oids: list (datatype_of_asn1_type OID) {valid_keyPurposeIDs oids})
  (x: x509_ext_key_usage_t oids)
: GTot (_)
  (decreases (List.length oids))
= let oids', oid = List.Tot.Base.unsnoc oids in
  List.Tot.Properties.lemma_unsnoc_length oids;
  match oids' with
  | [] -> ( serialize (serialize_asn1_oid_TLV_of oid) x )
  | _  -> ( let x = x <: x509_ext_key_usage_t oids' `tuple2` get_parser_type (parse_asn1_oid_TLV_of oid) in
            serialize_x509_ext_key_usage_unfold_spec oids' (fst x)
            `Seq.append`
            serialize (serialize_asn1_oid_TLV_of oid) (snd x) )

let rec lemma_serialize_x509_ext_key_usage_unfold
  (oids: list (datatype_of_asn1_type OID) {valid_keyPurposeIDs oids})
  (x: x509_ext_key_usage_t oids)
: Lemma (ensures
  serialize (serialize_x509_ext_key_usage oids) x ==
  serialize_x509_ext_key_usage_unfold_spec oids x
)
  (decreases (List.length oids))
= let oids', oid = List.Tot.Base.unsnoc oids in
  List.Tot.Properties.lemma_unsnoc_length oids;
  match oids' with
  | [] -> ()
  | _  -> ( let x = x <: x509_ext_key_usage_t oids' `tuple2` get_parser_type (parse_asn1_oid_TLV_of oid) in
            serialize_nondep_then_eq
            (* s1 *) (serialize_x509_ext_key_usage oids')
            (* s2 *) (serialize_asn1_oid_TLV_of oid)
            (* in *) x;
            lemma_serialize_x509_ext_key_usage_unfold oids' (fst x) )

let rec serialize_x509_ext_key_usage_size_spec
  (oids: list (datatype_of_asn1_type OID) {valid_keyPurposeIDs oids})
  (x: x509_ext_key_usage_t oids)
: GTot (nat)
  (decreases (List.length oids))
= let oids', oid = List.Tot.Base.unsnoc oids in
  List.Tot.Properties.lemma_unsnoc_length oids;
  match oids' with
  | [] -> ( Seq.length (serialize (serialize_asn1_oid_TLV_of oid) x) )
  | _  -> ( let x = x <: x509_ext_key_usage_t oids' `tuple2` get_parser_type (parse_asn1_oid_TLV_of oid) in
            serialize_x509_ext_key_usage_size_spec oids' (fst x)  +
            Seq.length (serialize (serialize_asn1_oid_TLV_of oid) (snd x)) )

let rec lemma_serialize_x509_ext_key_usage_size
  (oids: list (datatype_of_asn1_type OID) {valid_keyPurposeIDs oids})
  (x: x509_ext_key_usage_t oids)
: Lemma (ensures
  Seq.length (serialize (serialize_x509_ext_key_usage oids) x) ==
  serialize_x509_ext_key_usage_size_spec oids x
)
  (decreases (List.length oids))
= lemma_serialize_x509_ext_key_usage_unfold oids x;
  let oids', oid = List.Tot.Base.unsnoc oids in
  List.Tot.Properties.lemma_unsnoc_length oids;
  match oids' with
  | [] -> ()
  | _  -> ( let x = x <: x509_ext_key_usage_t oids' `tuple2` get_parser_type (parse_asn1_oid_TLV_of oid) in
            lemma_serialize_x509_ext_key_usage_unfold oids' (fst x);
            lemma_serialize_x509_ext_key_usage_size oids' (fst x) )

(* Sequence enveloped with OID *)
let parse_x509_ext_key_usage_sequence_TLV
  (oids: list (datatype_of_asn1_type OID) {valid_keyPurposeIDs oids})
= parse_asn1_sequence_TLV
    (OID_EXTENDED_KEY_USAGE
     `serialize_envelop_OID_with`
     serialize_x509_ext_key_usage oids)

let serialize_x509_ext_key_usage_sequence_TLV
  (oids: list (datatype_of_asn1_type OID) {valid_keyPurposeIDs oids})
: serializer (parse_x509_ext_key_usage_sequence_TLV oids)
= serialize_asn1_sequence_TLV
    (OID_EXTENDED_KEY_USAGE
     `serialize_envelop_OID_with`
     serialize_x509_ext_key_usage oids)

let lemma_serialize_x509_ext_key_usage_sequence_TLV_unfold
  (oids: list (datatype_of_asn1_type OID) {valid_keyPurposeIDs oids})
= lemma_serialize_asn1_sequence_TLV_unfold
    (OID_EXTENDED_KEY_USAGE
     `serialize_envelop_OID_with`
     serialize_x509_ext_key_usage oids)

let lemma_serialize_x509_ext_key_usage_sequence_TLV_size
  (oids: list (datatype_of_asn1_type OID) {valid_keyPurposeIDs oids})
= lemma_serialize_asn1_sequence_TLV_size
    (OID_EXTENDED_KEY_USAGE
     `serialize_envelop_OID_with`
     serialize_x509_ext_key_usage oids)

(* 1 *)
let parse_x509_ext_key_usage_1
  (oid: datatype_of_asn1_type OID)
: parser _ _
= parse_asn1_oid_TLV_of oid

let serialize_x509_ext_key_usage_1
  (oid: datatype_of_asn1_type OID)
: serializer (parse_x509_ext_key_usage_1 oid)
= serialize_asn1_oid_TLV_of oid

let lemma_serialize_x509_ext_key_usage_1_unfold
  (oid: datatype_of_asn1_type OID)
= lemma_serialize_asn1_oid_TLV_unfold oid

let lemma_serialize_x509_ext_key_usage_1_size
  (oid: datatype_of_asn1_type OID)
= lemma_serialize_asn1_oid_TLV_size oid

let parse_x509_ext_key_usage_1_sequence_TLV
  (oid: datatype_of_asn1_type OID)
= parse_asn1_sequence_TLV
    (OID_EXTENDED_KEY_USAGE
     `serialize_envelop_OID_with`
     serialize_x509_ext_key_usage_1 oid)

let serialize_x509_ext_key_usage_1_sequence_TLV
  (oid: datatype_of_asn1_type OID)
: serializer (parse_x509_ext_key_usage_1_sequence_TLV oid)
= serialize_asn1_sequence_TLV
    (OID_EXTENDED_KEY_USAGE
     `serialize_envelop_OID_with`
     serialize_x509_ext_key_usage_1 oid)

let lemma_serialize_x509_ext_key_usage_1_sequence_TLV_unfold
  (oid: datatype_of_asn1_type OID)
= lemma_serialize_asn1_sequence_TLV_unfold
    (OID_EXTENDED_KEY_USAGE
     `serialize_envelop_OID_with`
     serialize_x509_ext_key_usage_1 oid)

let lemma_serialize_x509_ext_key_usage_1_sequence_TLV_size
  (oid: datatype_of_asn1_type OID)
= lemma_serialize_asn1_sequence_TLV_size
    (OID_EXTENDED_KEY_USAGE
     `serialize_envelop_OID_with`
     serialize_x509_ext_key_usage_1 oid)

open ASN1.Low
let x509_ext_key_usage_1_inbound
  (oid: datatype_of_asn1_type OID)
= inbound_sequence_value_of (serialize_x509_ext_key_usage_1 oid)

let x509_ext_key_usage_t_inbound
  (oids: list (datatype_of_asn1_type OID) {valid_keyPurposeIDs oids})
= inbound_sequence_value_of (serialize_x509_ext_key_usage oids)

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module MB = LowStar.Monotonic.Buffer
module B = LowStar.Buffer
module Cast = FStar.Int.Cast

module B32 = FStar.Bytes

module IB = LowStar.ImmutableBuffer
module CB = LowStar.ConstBuffer

module G = FStar.Ghost
open FStar.Integers

// #push-options "--z3rlimit 16"
// let rec length_of_x509_ext_key_usage
//   (oids: list (datatype_of_asn1_type OID) { valid_keyPurposeIDs oids})
//   (x: x509_ext_key_usage_t oids)
// : GTot (l: nat {l == Seq.length (serialize (serialize_x509_ext_key_usage oids) x)})
//   (decreases (List.length oids))
// = lemma_serialize_x509_ext_key_usage_unfold oids x;
//   lemma_serialize_x509_ext_key_usage_size   oids x;
//   let oids', oid = List.Tot.Base.unsnoc oids in
//   List.Tot.Properties.lemma_unsnoc_length oids;
//   match oids' with
//   | [] -> ( let x = x <: datatype_of_asn1_type OID in
//             length_of_asn1_primitive_TLV x  )
//   | _  -> ( let x = x <: x509_ext_key_usage_t oids' `tuple2` get_parser_type (parse_asn1_oid_TLV_of oid) in
//             length_of_x509_ext_key_usage oids' (fst x) +
//             length_of_asn1_primitive_TLV #OID (snd x) )

(* NOTE: Expect all instantiations of it be marked as `inline_for_extraction` evaluated at extract time *)
(* TODO: Check actual extraction behavior. *)
noextract
let rec serialize32_x509_ext_key_usage_backwards
  (oids: list (datatype_of_asn1_type OID) {valid_keyPurposeIDs oids})
: Tot (serializer32_backwards (serialize_x509_ext_key_usage oids))
  (decreases (List.length oids))
= let oids', oid = List.Tot.Base.unsnoc oids in
  List.Tot.Properties.lemma_unsnoc_length oids;
  match oids' with
  | [] -> ( serialize32_asn1_oid_TLV_of_backwards oid )
  | _  -> ( serialize32_x509_ext_key_usage_backwards oids'
            `serialize32_nondep_then_backwards`
            serialize32_asn1_oid_TLV_of_backwards oid )

noextract
let serialize32_x509_ext_key_usage_sequence_TLV_backwards
  (oids: list (datatype_of_asn1_type OID) {valid_keyPurposeIDs oids})
: serializer32_backwards (serialize_x509_ext_key_usage_sequence_TLV oids)
= serialize32_asn1_sequence_TLV_backwards
  (* s32 *) (OID_EXTENDED_KEY_USAGE
             `serialize32_envelop_OID_with_backwards`
             serialize32_x509_ext_key_usage_backwards oids)
