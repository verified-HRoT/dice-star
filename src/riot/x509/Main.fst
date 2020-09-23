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

#set-options "--z3rlimit 32 --fuel 4 --ifuel 0"

noextract unfold inline_for_extraction
let oids: l: list (datatype_of_asn1_type OID) { valid_keyPurposeIDs l }
= [@inline_let] let l = [OID_AT_CN; OID_AT_COUNTRY; OID_AT_ORGANIZATION] in
  assert_norm (valid_keyPurposeIDs l);
  l

// [@@T.postprocess_with (postprocess_x509_keyPurposeIDs (`%oids))]
// let ty = x509_keyPurposeIDs_t oids

(* It works when inlining those types *)
// [@@T.postprocess_with (postprocess_x509_keyPurposeIDs (`%oids))]
// let exty = x509_ext_key_usage_t oids

#push-options "--fuel 4"
[@@T.postprocess_with (postprocess_x509_keyPurposeIDs (`%oids))]
let main ()
: HST.ST C.exit_code
  (requires fun h -> True)
  (ensures fun _ _ _ -> True)
=
  HST.push_frame ();
  let b = B.alloca 0uy 100ul in
  let tm: x509_keyPurposeIDs_t oids = get_x509_keyPurposeIDs oids in
  (* Prf *) lemma_serialize_x509_keyPurposeIDs_size oids tm;
  let extm: x509_ext_key_usage_t oids = x509_get_ext_extendedKeyUsage oids true in
  (* Prf *) lemma_serialize_x509_ext_key_usage_size_exact oids extm;
  let r = serialize32_x509_keyPurposeIDs_backwards oids tm b 50ul in
  let r = serialize32_x509_ext_key_usage_backwards oids extm b 50ul in
  HST.pop_frame ();
  C.EXIT_SUCCESS
