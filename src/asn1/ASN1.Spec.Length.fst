module ASN1.Spec.Length

open LowParse.Spec.Base
open LowParse.Spec.Combinators
open LowParse.Spec.DER

open ASN1.Base

let asn1_int32 = bounded_int32 asn1_length_min asn1_length_max

let parse_asn1_length_kind = parse_bounded_der_length32_kind asn1_length_min asn1_length_max

let parse_asn1_length
: parser parse_asn1_length_kind asn1_int32
= parse_bounded_der_length32 asn1_length_min asn1_length_max

let parse_asn1_length_unfold = parse_bounded_der_length32_unfold asn1_length_min asn1_length_max

let serialize_asn1_length
: serializer parse_asn1_length
= serialize_bounded_der_length32 asn1_length_min asn1_length_max

let serialize_asn1_length_unfold = serialize_bounded_der_length32_unfold asn1_length_min asn1_length_max
