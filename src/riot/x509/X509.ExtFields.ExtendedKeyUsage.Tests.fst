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

#set-options "--z3rlimit 32 --fuel 4 --ifuel 0"

noextract inline_for_extraction
let oids
: l: keyPurposeIDs_oids_t
     { valid_x509_ext_key_usage_ingredients l }
= [@inline_let] let l = [OID_AT_CN; OID_AT_COUNTRY; OID_AT_ORGANIZATION] in
  assert_norm (valid_keyPurposeIDs l);
  lemma_serialize_x509_keyPurposeIDs_size l;
  l

#set-options "--fuel 0"

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


[@@T.postprocess_with (postprocess_x509_keyPurposeIDs (`%oids))]
let ty = x509_keyPurposeIDs_t oids

let tm: ty = ((OID_AT_CN, OID_AT_COUNTRY), OID_AT_ORGANIZATION)

let p = parse_x509_keyPurposeIDs oids

let s = serialize_x509_keyPurposeIDs oids

// let lemma_serialize_x509_keyPurposeIDs_unfold_test ()
// : Lemma (
//  s `serialize` tm ==
//  (serialize_asn1_oid_TLV_of OID_AT_CN `serialize` (fst (fst tm)))
//   `Seq.append`
//  (serialize_asn1_oid_TLV_of OID_AT_COUNTRY `serialize` (snd (fst tm)))
//   `Seq.append`
//  (serialize_asn1_oid_TLV_of OID_AT_ORGANIZATION `serialize` (snd tm))
// )
// = //P.norm_spec (norm_steps_x509_keyPurposeIDs (`%oids)) (serialize_x509_keyPurposeIDs_unfold_spec oids tm);
//   lemma_x509_keyPurposeIDs_unique oids;
//   lemma_serialize_x509_keyPurposeIDs_unfold_norm oids;
//   lemma_serialize_x509_keyPurposeIDs_unfold oids


[@@T.postprocess_with (postprocess_x509_keyPurposeIDs (`%oids))]
let y = len_of_x509_keyPurposeIDs oids

let z = normalize_term y

#push-options "--z3rlimit 256 --fuel 0 --ifuel 0"
// [@@T.postprocess_with (postprocess_x509_keyPurposeIDs (`%oids))]
let lemma_serialize_x509_keyPurposeIDs_size_test ()
: Lemma (
  // let ty = P.norm_spec (norm_steps_x509_keyPurposeIDs (`%oids)) (x509_keyPurposeIDs_t oids);
  //          P.norm      (norm_steps_x509_keyPurposeIDs (`%oids)) (x509_keyPurposeIDs_t oids) in
  // let tm: ty = ((OID_AT_CN, OID_AT_COUNTRY), OID_AT_ORGANIZATION) in
 // length_of_opaque_serialization s tm < 100
 // serialize_x509_keyPurposeIDs_size_spec oids < 100
 // P.norm
 //   (norm_steps_x509_keyPurposeIDs (`%oids))
   (length_of_x509_keyPurposeIDs oids) < 100
)
=
  (* FIXME: Don't know why but this lemma is not working. *)
  // lemma_length_of_x509_keyPurposeIDs_norm oids;
  P.norm_spec
   (norm_steps_x509_keyPurposeIDs (`%oids))
   (length_of_x509_keyPurposeIDs oids)
(*)
;

//admit();
  // let ty = (x509_keyPurposeIDs_t oids) in
  // let tm: ty = ((OID_AT_CN, OID_AT_COUNTRY), OID_AT_ORGANIZATION) in
  //P.norm_spec (norm_steps_x509_keyPurposeIDs (`%oids)) (serialize_x509_keyPurposeIDs_unfold_spec oids tm);
  // lemma_serialize_x509_keyPurposeIDs_size_norm oids;
  // lemma_serialize_x509_keyPurposeIDs_size oids
  lemma_length_of_x509_keyPurposeIDs_norm oids
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
