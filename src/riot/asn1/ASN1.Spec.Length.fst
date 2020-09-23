module ASN1.Spec.Length

open ASN1.Spec.Base
open LowParse.Spec.DER
open FStar.Integers

open ASN1.Base

#set-options "--z3rlimit 32 --fuel 0 --ifuel 0"

/// ASN1 length parser, based on `LowParse.Spec.DER`

/// Generic
///
inline_for_extraction noextract
let parse_asn1_length_kind = parse_bounded_der_length32_kind asn1_length_min asn1_length_max

noextract
let parse_asn1_length
: parser parse_asn1_length_kind asn1_int32
= parse_bounded_der_length32 asn1_length_min asn1_length_max

noextract
let lemma_parse_asn1_length_unfold = parse_bounded_der_length32_unfold asn1_length_min asn1_length_max

noextract
let serialize_asn1_length
: serializer parse_asn1_length
= serialize_bounded_der_length32 asn1_length_min asn1_length_max

noextract
let lemma_serialize_asn1_length_unfold = serialize_bounded_der_length32_unfold asn1_length_min asn1_length_max

noextract
let lemma_serialize_asn1_length_size = serialize_bounded_der_length32_size asn1_length_min asn1_length_max


inline_for_extraction noextract
let parse_asn1_length_of_bound_kind
  (min: asn1_length_t)
  (max: asn1_length_t { min <= max })
: parser_kind
= parse_bounded_der_length32_kind min max

let parse_asn1_length_of_bound
  (min: asn1_length_t)
  (max: asn1_length_t { min <= max })
: parser (parse_asn1_length_of_bound_kind min max) (bounded_int32 min max)
= parse_bounded_der_length32 min max

let serialize_asn1_length_of_bound
  (min: asn1_length_t)
  (max: asn1_length_t { min <= max })
: serializer (parse_asn1_length_of_bound min max)
= serialize_bounded_der_length32 min max

let lemma_serialize_asn1_length_of_bound_unfold
  (min: asn1_length_t)
  (max: asn1_length_t { min <= max })
= serialize_bounded_der_length32_unfold min max

let lemma_serialize_asn1_length_of_bound_size
  (min: asn1_length_t)
  (max: asn1_length_t { min <= max })
= serialize_bounded_der_length32_size min max

noextract
let length_of_asn1_length
  (len: asn1_int32)
: GTot (length: asn1_length_t
       { length == Seq.length (serialize serialize_asn1_length len) /\
         length <= 5 })
= lemma_serialize_asn1_length_unfold len;
  lemma_serialize_asn1_length_size len;
  let x = tag_of_der_length32 len in
  if x < 128uy then
  ( 1 )
  else if x = 129uy then
  ( 2 )
  else if x = 130uy then
  ( 3 )
  else if x = 131uy then
  ( 4 )
  else
  ( 5 )

/// Specialized for a specific ASN1 type
///

inline_for_extraction noextract
let parse_asn1_length_kind_of_type
  (_a: asn1_tag_t)
: parser_kind
= parse_bounded_der_length32_kind (asn1_value_length_min_of_type _a) (asn1_value_length_max_of_type _a)

inline_for_extraction noextract
let parse_asn1_length_of_type
  (_a: asn1_tag_t)
: parser (parse_asn1_length_kind_of_type _a) (asn1_value_int32_of_type _a)
= parse_bounded_der_length32 (asn1_value_length_min_of_type _a) (asn1_value_length_max_of_type _a)

inline_for_extraction noextract
let serialize_asn1_length_of_type
  (_a: asn1_tag_t)
: serializer (parse_asn1_length_of_type _a)
= serialize_bounded_der_length32 (asn1_value_length_min_of_type _a) (asn1_value_length_max_of_type _a)

/// NOTE: Since we cannot simply define them (the refinement in the return types will lose),
///       not definint them for now.
// noextract
// let lemma_parse_asn1_length_of_type_unfold
//   (_a: asn1_tag_t)
//   (input: bytes)
// = parse_bounded_der_length32_unfold (asn1_value_length_min_of_type _a) (asn1_value_length_max_of_type _a) input

// noextract
// let lemma_serialize_asn1_length_of_type_unfold
//   (_a: asn1_tag_t)
//   (len: asn1_value_int32_of_type _a)
// = serialize_bounded_der_length32_unfold (asn1_value_length_min_of_type _a) (asn1_value_length_max_of_type _a) len

// noextract
// let lemma_serialize_asn1_length_of_type_size
//   (_a: asn1_tag_t)
//   (len: asn1_value_int32_of_type _a)
// = serialize_bounded_der_length32_size (asn1_value_length_min_of_type _a) (asn1_value_length_max_of_type _a) len

/// NOTE: Use this with `lemma_serialize_asn1_length_unfold/size` when you need to prove something in the serialization.
let serialize_asn1_length_of_bound_eq
  (min: asn1_length_t)
  (max: asn1_length_t { min <= max })
  (len: bounded_int32 min max)
: Lemma (
  serialize serialize_asn1_length len ==
  serialize (serialize_asn1_length_of_bound min max) len
)
= lemma_serialize_asn1_length_of_bound_unfold min max len;
  serialize_bounded_der_length32_unfold asn1_length_min asn1_length_max len

let serialize_asn1_length_of_type_eq
  (_a: asn1_tag_t)
  (len: asn1_value_int32_of_type _a)
: Lemma (
  serialize serialize_asn1_length len ==
  serialize (serialize_asn1_length_of_type _a) len
)
= lemma_serialize_asn1_length_unfold len;
  let min, max = asn1_value_length_min_of_type _a, asn1_value_length_max_of_type _a in
  serialize_bounded_der_length32_unfold min max len

