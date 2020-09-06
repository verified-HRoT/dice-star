module X509.ExtFields.ExtendedKeyUsage.Tests

open LowParse.Spec.Base
open LowParse.Spec.Combinators

open ASN1.Base
open ASN1.Spec
open ASN1.Low

open X509.Base
open FStar.Integers
module B32 = FStar.Bytes

module T = FStar.Tactics
module P = FStar.Pervasives

open X509.ExtFields.ExtendedKeyUsage

noextract unfold inline_for_extraction
let oids: l: list (datatype_of_asn1_type OID) { valid_keyPurposeIDs l }
= [@inline_let] let l = [OID_AT_CN; OID_AT_COUNTRY; OID_AT_ORGANIZATION] in
  assert_norm (valid_keyPurposeIDs l);
  l

// noextract
// let norm_kp () : Tac unit = norm [delta_only [
//   `%x509_keyPurposeIDs_t;
//   `%oids;
//   `%serialize_x509_keyPurposeIDs_unfold_spec;
//   `%lemma_serialize_x509_keyPurposeIDs_unfold;
//   `%FStar.List.Tot.Base.unsnoc;
//   `%FStar.List.Tot.Base.splitAt;
//   `%FStar.List.Tot.Base.length;
//   `%FStar.List.Tot.Base.hd;
// ]; primops; zeta; iota]; trefl ()

(*)
#push-options "--fuel 0 --ifuel 0"
// [@@T.postprocess_with (postprocess_x509_keyPurposeIDs (`%oids))]
let ty = P.norm      (norm_steps_x509_keyPurposeIDs (`%oids)) (x509_keyPurposeIDs_t oids)

[@expect_failure]
let test_fail
= let ty = P.norm      (norm_steps_x509_keyPurposeIDs (`%oids)) (x509_keyPurposeIDs_t oids) in
  let tm: ty = ((OID_AT_CN, OID_AT_COUNTRY), OID_AT_ORGANIZATION) in
()

let test_success
= //let ty = P.norm      (norm_steps_x509_keyPurposeIDs (`%oids)) (x509_keyPurposeIDs_t oids) in
  let tm: ty = ((OID_AT_CN, OID_AT_COUNTRY), OID_AT_ORGANIZATION) in
()

let tm: ty = ((OID_AT_CN, OID_AT_COUNTRY), OID_AT_ORGANIZATION)

let p = parse_x509_keyPurposeIDs oids

let s = serialize_x509_keyPurposeIDs oids

let lemma_serialize_x509_keyPurposeIDs_unfold_test ()
: Lemma (
 s `serialize` tm ==
 (serialize_asn1_oid_TLV_of OID_AT_CN `serialize` (fst (fst tm)))
  `Seq.append`
 (serialize_asn1_oid_TLV_of OID_AT_COUNTRY `serialize` (snd (fst tm)))
  `Seq.append`
 (serialize_asn1_oid_TLV_of OID_AT_ORGANIZATION `serialize` (snd tm))
)
= //P.norm_spec (norm_steps_x509_keyPurposeIDs (`%oids)) (serialize_x509_keyPurposeIDs_unfold_spec oids tm);
  lemma_serialize_x509_keyPurposeIDs_unfold_norm oids tm;
  lemma_serialize_x509_keyPurposeIDs_unfold oids tm

#push-options "--z3rlimit 32 --fuel 0 --ifuel 0"
// [@@T.postprocess_with (postprocess_x509_keyPurposeIDs (`%oids))]
[@expect_failure]
let lemma_serialize_x509_keyPurposeIDs_size_test ()
: Lemma (
  // let ty = P.norm_spec (norm_steps_x509_keyPurposeIDs (`%oids)) (x509_keyPurposeIDs_t oids);
  //          P.norm      (norm_steps_x509_keyPurposeIDs (`%oids)) (x509_keyPurposeIDs_t oids) in
  let tm: ty = ((OID_AT_CN, OID_AT_COUNTRY), OID_AT_ORGANIZATION) in
 // length_of_opaque_serialization s tm < 100
 serialize_x509_keyPurposeIDs_size_spec oids tm < 100
)
= admit();
  let ty = (x509_keyPurposeIDs_t oids) in
  let tm: ty = ((OID_AT_CN, OID_AT_COUNTRY), OID_AT_ORGANIZATION) in
  //P.norm_spec (norm_steps_x509_keyPurposeIDs (`%oids)) (serialize_x509_keyPurposeIDs_unfold_spec oids tm);
  lemma_serialize_x509_keyPurposeIDs_size_norm oids tm;
  lemma_serialize_x509_keyPurposeIDs_size oids tm
  // lemma_serialize_asn1_oid_TLV_of_size OID_AT_CN OID_AT_CN;
  // lemma_serialize_asn1_oid_TLV_of_size OID_AT_COUNTRY OID_AT_COUNTRY;
  // lemma_serialize_asn1_oid_TLV_of_size OID_AT_ORGANIZATION OID_AT_ORGANIZATION

// [@@postprocess_with norm_kp]
// let prop ()
// =
//   norm_spec [delta_only [
//   `%x509_keyPurposeIDs_t;
//   `%oids;
//   `%serialize_x509_keyPurposeIDs_unfold_spec;
//   `%lemma_serialize_x509_keyPurposeIDs_unfold;
//   `%FStar.List.Tot.Base.unsnoc;
//   `%FStar.List.Tot.Base.splitAt;
//   `%FStar.List.Tot.Base.length;
//   `%FStar.List.Tot.Base.hd;
// ]; primops; zeta; iota] (serialize s tm == serialize_x509_keyPurposeIDs_unfold_spec oids tm)
// = (lemma_serialize_x509_keyPurposeIDs_unfold oids tm)
