module ASN1.Spec.Length

open LowParse.Spec.Base
open LowParse.Spec.Combinators
open LowParse.Spec.DER
open FStar.Integers

open ASN1.Base

/// ASN1 length parser, based on `LowParse.Spec.DER`

/// Generic
///
inline_for_extraction
let parse_asn1_length_kind = parse_bounded_der_length32_kind asn1_length_min asn1_length_max

noextract
let parse_asn1_length
: parser parse_asn1_length_kind asn1_int32
= parse_bounded_der_length32 asn1_length_min asn1_length_max

noextract
let parse_asn1_length_unfold = parse_bounded_der_length32_unfold asn1_length_min asn1_length_max

noextract
let serialize_asn1_length
: serializer parse_asn1_length
= serialize_bounded_der_length32 asn1_length_min asn1_length_max

noextract
let serialize_asn1_length_unfold = serialize_bounded_der_length32_unfold asn1_length_min asn1_length_max

noextract
let serialize_asn1_length_size = serialize_bounded_der_length32_size asn1_length_min asn1_length_max

#push-options "--z3rlimit 16"
noextract
let length_of_asn1_length
  (len: asn1_int32)
: GTot (length: asn1_length_t{length == Seq.length (serialize serialize_asn1_length len)})
= serialize_asn1_length_unfold len;
  serialize_asn1_length_size len;
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
#pop-options

/// Specialized for a specific ASN1 type
///

inline_for_extraction
let parse_asn1_length_kind_of_type
  (_a: asn1_type)
: parser_kind
= parse_bounded_der_length32_kind (asn1_value_length_min_of_type _a) (asn1_value_length_max_of_type _a)

noextract
let parse_asn1_length_of_type
  (_a: asn1_type)
: parser (parse_asn1_length_kind_of_type _a) (asn1_value_int32_of_type _a)
= parse_bounded_der_length32 (asn1_value_length_min_of_type _a) (asn1_value_length_max_of_type _a)

noextract
let serialize_asn1_length_of_type
  (_a: asn1_type)
: serializer (parse_asn1_length_of_type _a)
= serialize_bounded_der_length32 (asn1_value_length_min_of_type _a) (asn1_value_length_max_of_type _a)

/// NOTE: Since we cannot simply define them (the refinement in the return types will lose),
///       not definint them for now.
// noextract
// let parse_asn1_length_of_type_unfold
//   (_a: asn1_type)
//   (input: bytes)
// = parse_bounded_der_length32_unfold (asn1_value_length_min_of_type _a) (asn1_value_length_max_of_type _a) input

// noextract
// let serialize_asn1_length_of_type_unfold
//   (_a: asn1_type)
//   (len: asn1_value_int32_of_type _a)
// = serialize_bounded_der_length32_unfold (asn1_value_length_min_of_type _a) (asn1_value_length_max_of_type _a) len

// noextract
// let serialize_asn1_length_of_type_size
//   (_a: asn1_type)
//   (len: asn1_value_int32_of_type _a)
// = serialize_bounded_der_length32_size (asn1_value_length_min_of_type _a) (asn1_value_length_max_of_type _a) len

/// NOTE: Use this with `serialize_asn1_length_unfold/size` when you need to prove something in the serialization.
noextract
let serialize_asn1_length_of_type_eq
  (_a: asn1_type)
  (len: asn1_value_int32_of_type _a)
: Lemma (
  serialize serialize_asn1_length len ==
  serialize (serialize_asn1_length_of_type _a) len
)
= serialize_asn1_length_unfold len;
  let min, max = asn1_value_length_min_of_type _a, asn1_value_length_max_of_type _a in
  serialize_bounded_der_length32_unfold min max len

