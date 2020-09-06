module Main

(*)
open LowParse.Spec.Base
open LowParse.Spec.Combinators

open ASN1.Base
open ASN1.Spec
open ASN1.Low

open X509.Base
open X509.ExtFields.ExtendedKeyUsage

module B32 = FStar.Bytes

open LowStar.Comment
open LowStar.Printf
module Fail = LowStar.Failure
module B = LowStar.Buffer
module IB = LowStar.ImmutableBuffer
module HS  = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B32 = FStar.Bytes

module T = FStar.Tactics
module P = FStar.Pervasives

#set-options "--z3rlimit 32 --fuel 0 --ifuel 0"

noextract unfold inline_for_extraction
let oids: l: list (datatype_of_asn1_type OID) { valid_keyPurposeIDs l }
= [@inline_let] let l = [OID_AT_CN; OID_AT_COUNTRY; OID_AT_ORGANIZATION] in
  assert_norm (valid_keyPurposeIDs l);
  l

// noextract
// let norm_kp () : Tac unit = norm [delta_only [
//   `%x509_keyPurposeIDs_t;
//   `%oids;
//   `%FStar.List.Tot.Base.unsnoc;
//   `%FStar.List.Tot.Base.splitAt;
//   `%FStar.List.Tot.Base.length
// ]; primops; zeta; iota]; trefl ()

[@@T.postprocess_with (postprocess_x509_keyPurposeIDs (`%oids))]
let ty = (x509_keyPurposeIDs_t oids)

// [@@T.postprocess_with (postprocess_x509_keyPurposeIDs (`%oids))]
// noextract inline_for_extraction
// let tm: ty = get_x509_keyPurposeIDs oids

[@@T.postprocess_with (postprocess_x509_keyPurposeIDs (`%oids))]
let exty = (x509_ext_key_usage_t oids)

// #push-options "--fuel 4"
// let extm: exty
// =
//   lemma_serialize_x509_keyPurposeIDs_size_norm oids tm;
//   lemma_serialize_x509_keyPurposeIDs_size oids tm;
//   x509_get_ext_extendedKeyUsage oids true
// #pop-options

let p = parse_x509_keyPurposeIDs oids

let s = serialize_x509_keyPurposeIDs oids

[@@T.postprocess_with (postprocess_x509_keyPurposeIDs (`%oids))]
noextract inline_for_extraction
let s32 = serialize32_x509_keyPurposeIDs_backwards oids

[@@T.postprocess_with (postprocess_x509_keyPurposeIDs (`%oids))]
let x =
  let x = 1 in
  let y = (x509_ext_key_usage_t oids) in
  y

open X509.BasicFields.Extension2
let norm_steps_x509_keyPurposeIDs
  (oids_name: string)
: list P.norm_step
= [delta_only [
(* the parameter *)
  oids_name;
(* the type to extract *)
  `%x509_keyPurposeIDs_t;
  `%get_x509_keyPurposeIDs;
  `%x509_ext_key_usage_payload_t;
  `%x509_ext_key_usage_t;
  `%x509_extension_payload_t;
  `%x509_extension_t;
  // `%serialize_x509_ext_key_usage_payload;
  // `%serialize_x509_keyPurposeIDs;
  `%inbound_sequence_value_of;
  `%inbound_envelop_tag_with_value_of;
  (* the Low* implementation to extract *)
  `%serialize32_x509_keyPurposeIDs_backwards;
  `%serialize_x509_keyPurposeIDs_size_spec;
  `%length_of_x509_keyPurposeIDs;
  `%len_of_x509_keyPurposeIDs;
  `%length_of_x509_ext_key_usage;
  `%len_of_x509_ext_key_usage_payload;
  `%length_of_x509_ext_key_usage_payload;
  `%len_of_x509_ext_key_usage;
  `%length_of_x509_ext_key_usage;
  `%x509_get_ext_extendedKeyUsage;
(* the specs and lemmas *)
  `%serialize_x509_keyPurposeIDs_unfold_spec;
  `%serialize_x509_keyPurposeIDs_size_spec;
  `%predicate_serialize_x509_keyPurposeIDs_size_oids;
  `%lemma_serialize_x509_keyPurposeIDs_unfold;
  `%lemma_serialize_x509_keyPurposeIDs_size;
(* list ops *)
  `%FStar.List.Tot.Base.unsnoc;
  `%FStar.List.Tot.Base.splitAt;
  `%FStar.List.Tot.Base.length;
  `%FStar.List.Tot.Base.hd;
(* coerce helpers *)
  // `%coerce_parser;
  // `%coerce_parser_serializer;
  `%coerce_serializer32_backwards;
  ]; primops; zeta; iota]


let tm: ty = P.norm (norm_steps_x509_keyPurposeIDs (`%oids)) (get_x509_keyPurposeIDs oids)

#push-options "--fuel 4"
[@@T.postprocess_with (postprocess_x509_keyPurposeIDs (`%oids))]
let xx =
  // let tm: ty = P.norm (norm_steps_x509_keyPurposeIDs (`%oids)) (get_x509_keyPurposeIDs oids) in
  lemma_serialize_x509_keyPurposeIDs_size_norm oids tm;
  lemma_serialize_x509_keyPurposeIDs_size oids tm;
  assert (
    serialize_x509_keyPurposeIDs_size_spec oids tm <=
    asn1_value_length_max_of_type (SEQUENCE) /\
    length_of_x509_ext_key_usage_payload_unbound oids tm <=
    asn1_value_length_max_of_type (OCTET_STRING) /\
    length_of_opaque_serialization (serialize_x509_keyPurposeIDs oids) tm
    <= asn1_value_length_max_of_type SEQUENCE
  );
  // lemma_serialize_x509_ext_key_usage_payload_size_exact oids tm;
  len_of_x509_ext_key_usage_payload oids tm

let f ()
= let extm: exty = (x509_get_ext_extendedKeyUsage oids true) in
  1

// #push-options "--fuel 4"
let main ()
: HST.ST C.exit_code
  (requires fun h -> True)
  (ensures fun _ _ _ -> True)
=
  // HST.push_frame ();
  // let b = B.alloca 0uy 100ul in
  // let tm: ty = ((OID_AT_CN, OID_AT_COUNTRY), OID_AT_ORGANIZATION) in
  let tm: ty = P.norm (norm_steps_x509_keyPurposeIDs (`%oids)) (get_x509_keyPurposeIDs oids) in
  lemma_serialize_x509_keyPurposeIDs_size_norm oids tm;
  lemma_serialize_x509_keyPurposeIDs_size oids tm;
  assert (
    serialize_x509_keyPurposeIDs_size_spec oids tm <=
    asn1_value_length_max_of_type (SEQUENCE) /\
    length_of_x509_ext_key_usage_payload_unbound oids tm <=
    asn1_value_length_max_of_type (OCTET_STRING) /\
    length_of_opaque_serialization (serialize_x509_keyPurposeIDs oids) tm
    <= asn1_value_length_max_of_type SEQUENCE /\
   (let _ = lemma_serialize_x509_ext_key_usage_payload_size_exact oids tm in
    X509.BasicFields.Extension2.length_of_x509_extension_payload_unbounded
      (OID_EXTENDED_KEY_USAGE)
      (serialize_x509_ext_key_usage_payload oids)
      (tm)
      (P.norm (norm_steps_x509_keyPurposeIDs (`%oids)) length_of_x509_ext_key_usage_payload oids tm)
    <= asn1_value_length_max_of_type (SEQUENCE))
  );
  let extm: exty = P.norm_spec (norm_steps_x509_keyPurposeIDs (`%oids)) (x509_get_ext_extendedKeyUsage oids true);
                   P.norm      (norm_steps_x509_keyPurposeIDs (`%oids)) (x509_get_ext_extendedKeyUsage oids true) in
  // let tm2: ty = snd extm in
  // let r = s32 tm b 50ul in
  // HST.pop_frame ();
  C.EXIT_SUCCESS
