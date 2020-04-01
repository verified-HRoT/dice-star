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

let filter_asn1_length_of_tag
  (_a: asn1_type)
  (len: asn1_int32)
: GTot bool
= let l = v len in
  let min, max = min_of_asn1_type _a, max_of_asn1_type _a in
  asn1_length_inbound l min max

let asn1_int32_of_tag
  (_a: asn1_type)
// = parse_filter_refine (filter_asn1_length_of_tag _a)
= let min, max = min_of_asn1_type _a, max_of_asn1_type _a in
  bounded_int32 min max

let parse_asn1_length_kind_of_tag
  (_a: asn1_type)
: parser_kind
= let min, max = min_of_asn1_type _a, max_of_asn1_type _a in
  parse_bounded_der_length32_kind min max

let parse_asn1_length_of_tag
  (_a: asn1_type)
// : parser parse_asn1_length_kind (parse_filter_refine (filter_asn1_length_of_tag _a))
: parser (parse_asn1_length_kind_of_tag _a) (asn1_int32_of_tag _a)
= let min, max = min_of_asn1_type _a, max_of_asn1_type _a in
  parse_bounded_der_length32 min max
  // parse_asn1_length
  // `parse_filter`
  // filter_asn1_length_of_tag _a

let serialize_asn1_length_of_tag
  (_a: asn1_type)
: serializer (parse_asn1_length_of_tag _a)
= let min, max = min_of_asn1_type _a, max_of_asn1_type _a in
  serialize_bounded_der_length32 min max
// = serialize_asn1_length
//   `serialize_filter`
//   filter_asn1_length_of_tag _a
