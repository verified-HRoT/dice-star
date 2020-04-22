module ASN1.Spec.Length

open LowParse.Spec.Base
open LowParse.Spec.Combinators
open LowParse.Spec.DER
open FStar.Integers

open ASN1.Base

/// Generic
///
let parse_asn1_length_kind = parse_bounded_der_length32_kind asn1_length_min asn1_length_max

let parse_asn1_length
: parser parse_asn1_length_kind asn1_int32
= parse_bounded_der_length32 asn1_length_min asn1_length_max

let parse_asn1_length_unfold = parse_bounded_der_length32_unfold asn1_length_min asn1_length_max

let serialize_asn1_length
: serializer parse_asn1_length
= serialize_bounded_der_length32 asn1_length_min asn1_length_max

let serialize_asn1_length_unfold = serialize_bounded_der_length32_unfold asn1_length_min asn1_length_max


#push-options "--z3rlimit 16"
let len_of_asn1_length
  (len: asn1_int32)
: Tot (offset: uint_32{v offset == Seq.length (serialize serialize_asn1_length len)})
= serialize_asn1_length_unfold len;
  let x = tag_of_der_length32_impl len in
  if x < 128uy then
  ( 1ul )
  else if x = 129uy then
  ( 2ul )
  else if x = 130uy then
  ( 3ul )
  else if x = 131uy then
  ( 4ul )
  else
  ( 5ul )
#pop-options

/// Specialized
///

// let filter_asn1_length_of_type
//   (_a: asn1_type)
//   (len: asn1_int32)
// : GTot bool
// = let l = v len in
//   let min, max = asn1_length_min_of_type _a, asn1_length_max_of_type _a in
//   asn1_length_inbound l min max

let parse_asn1_length_kind_of_type
  (_a: asn1_type)
: parser_kind
= parse_bounded_der_length32_kind (asn1_length_min_of_type _a) (asn1_length_max_of_type _a)

let parse_asn1_length_of_type
  (_a: asn1_type)
// : parser parse_asn1_length_kind (parse_filter_refine (filter_asn1_length_of_type _a))
: parser (parse_asn1_length_kind_of_type _a) (asn1_int32_of_type _a)
= parse_bounded_der_length32 (asn1_length_min_of_type _a) (asn1_length_max_of_type _a)
  // parse_asn1_length
  // `parse_filter`
  // filter_asn1_length_of_type _a

let parse_asn1_length_of_type_unfold
  (_a: asn1_type)
  (input: bytes)
= parse_bounded_der_length32_unfold (asn1_length_min_of_type _a) (asn1_length_max_of_type _a) input

unfold
let serialize_asn1_length_of_type
  (_a: asn1_type)
: serializer (parse_asn1_length_of_type _a)
= serialize_bounded_der_length32 (asn1_length_min_of_type _a) (asn1_length_max_of_type _a)
// = serialize_asn1_length
//   `serialize_filter`
//   filter_asn1_length_of_type _a

// let serialize_asn1_length_of_type_unfold
//   (_a: asn1_type)
//   (len: asn1_int32_of_type _a)
// = serialize_bounded_der_length32_unfold (asn1_length_min_of_type _a) (asn1_length_max_of_type _a) len

// let serialize_asn1_length_of_type_size
//   (_a: asn1_type)
//   (len: asn1_int32_of_type _a)
// = serialize_bounded_der_length32_size (asn1_length_min_of_type _a) (asn1_length_max_of_type _a) len

let serialize_asn1_length_of_type_eq
  (_a: asn1_type)
  (len: asn1_int32_of_type _a)
: Lemma (
  serialize serialize_asn1_length len ==
  serialize (serialize_asn1_length_of_type _a) len
)
= serialize_asn1_length_unfold len;
  let min, max = asn1_length_min_of_type _a, asn1_length_max_of_type _a in
  serialize_bounded_der_length32_unfold min max len

// #push-options "--z3rlimit 16"
// let len_of_asn1_length_of_type
//   (_a: asn1_type)
//   (len: asn1_int32_of_type _a)
// : Tot (offset: uint_32{v offset == Seq.length (serialize (serialize_asn1_length_of_type _a) len)})
// = serialize_asn1_length_unfold len;
//   serialize_asn1_length_of_type_eq _a len;
//   let x = tag_of_der_length32_impl len in
//   if x < 128uy then
//   ( 1ul )
//   else if x = 129uy then
//   ( 2ul )
//   else if x = 130uy then
//   ( 3ul )
//   else if x = 131uy then
//   ( 4ul )
//   else
//   ( 5ul )
// #pop-options

