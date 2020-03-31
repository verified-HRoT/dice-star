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

/// Specialized
///

let filter_asn1_length_of_tag
  (_a: asn1_type)
  (len: asn1_int32)
: GTot bool
= let l = v len in
  let min, max = min_of_asn1_type _a, max_of_asn1_type _a in
  asn1_length_inbound l min max

let asn1_len_of_tag
  (_a: asn1_type)
= parse_filter_refine (filter_asn1_length_of_tag _a)

let parse_asn1_length_of_tag
  (_a: asn1_type)
: parser parse_asn1_length_kind (parse_filter_refine (filter_asn1_length_of_tag _a))
= parse_asn1_length
  `parse_filter`
  filter_asn1_length_of_tag _a

let serialize_asn1_length_of_tag
  (_a: asn1_type)
: serializer (parse_asn1_length_of_tag _a)
= serialize_asn1_length
  `serialize_filter`
  filter_asn1_length_of_tag _a
