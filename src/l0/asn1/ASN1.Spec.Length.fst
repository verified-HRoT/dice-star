module ASN1.Spec.Length

open ASN1.Spec.Base
open LowParse.Spec.DER
open FStar.Integers

open ASN1.Base

#set-options "--z3rlimit 32 --fuel 0 --ifuel 1"

/// ASN1 length parser, based on `LowParse.Spec.DER`


// let parse_asn1_length
// = parse_bounded_der_length32 asn1_length_min asn1_length_max

// noextract
// let lemma_parse_asn1_length_unfold = parse_bounded_der_length32_unfold asn1_length_min asn1_length_max

// let serialize_asn1_length
// = serialize_bounded_der_length32 asn1_length_min asn1_length_max

// let lemma_serialize_asn1_length_unfold y'
// = serialize_bounded_der_length32_unfold asn1_length_min asn1_length_max y'

// let lemma_serialize_asn1_length_size y'
// = serialize_bounded_der_length32_size asn1_length_min asn1_length_max y'

let parse_asn1_length_of_bound min max
= parse_bounded_der_length32 min max

let serialize_asn1_length_of_bound min max
= serialize_bounded_der_length32 min max

let lemma_serialize_asn1_length_of_bound_unfold min max
= serialize_bounded_der_length32_unfold min max

let lemma_serialize_asn1_length_of_bound_size min max
= serialize_bounded_der_length32_size min max

/// Specialized for a specific ASN1 type
///

// let parse_asn1_length_of_type _a
// = parse_bounded_der_length32 (asn1_value_length_min_of_type _a) (asn1_value_length_max_of_type _a)

// let serialize_asn1_length_of_type _a
// = serialize_bounded_der_length32 (asn1_value_length_min_of_type _a) (asn1_value_length_max_of_type _a

let serialize_asn1_length_of_bound_eq min max len
= lemma_serialize_asn1_length_of_bound_unfold min max len;
  serialize_bounded_der_length32_unfold asn1_length_min asn1_length_max len

let serialize_asn1_length_of_type_eq _a len
= lemma_serialize_asn1_length_unfold len;
  let min, max = asn1_value_length_min_of_type _a, asn1_value_length_max_of_type _a in
  serialize_bounded_der_length32_unfold min max len
