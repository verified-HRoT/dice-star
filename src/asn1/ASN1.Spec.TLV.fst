module ASN1.Spec.TLV

open LowParse.Spec.Base
open LowParse.Spec.Combinators

open ASN1.Base
open ASN1.Spec.Tag
open ASN1.Spec.Length
open ASN1.Spec.BOOLEAN
open ASN1.Spec.NULL
open ASN1.Spec.INTEGER
open ASN1.Spec.OCTET_STRING
open ASN1.Spec.BIT_STRING
open ASN1.Spec.SEQUENCE
open LowParse.Bytes

open FStar.Integers

/// Interfaces to make this library easier to use, WIP
///
noextract
let parse_asn1_TLV_kind_of_type
  (_a: asn1_primitive_type)
: parser_kind
= match _a with
  | BOOLEAN      -> parse_asn1_boolean_TLV_kind
  | NULL         -> parse_asn1_null_TLV_kind
  | INTEGER      -> parse_asn1_integer_TLV_kind
  | OCTET_STRING -> parse_asn1_octet_string_TLV_kind
  | BIT_STRING   -> parse_asn1_bit_string_TLV_kind
  | OID          -> admit ()

noextract
let parse_asn1_TLV_of_type
  (_a: asn1_primitive_type)
: parser (parse_asn1_TLV_kind_of_type _a) (datatype_of_asn1_type _a)
= match _a with
  | BOOLEAN      -> parse_asn1_boolean_TLV
  | NULL         -> parse_asn1_null_TLV
  | INTEGER      -> parse_asn1_integer_TLV
  | OCTET_STRING -> parse_asn1_octet_string_TLV
  | BIT_STRING   -> parse_asn1_bit_string_TLV
  | OID          -> admit ()

noextract
let serialize_asn1_TLV_of_type
  (_a: asn1_primitive_type)
: serializer (parse_asn1_TLV_of_type _a)
= match _a with
  | BOOLEAN      -> serialize_asn1_boolean_TLV
  | NULL         -> serialize_asn1_null_TLV
  | INTEGER      -> serialize_asn1_integer_TLV
  | OCTET_STRING -> serialize_asn1_octet_string_TLV
  | BIT_STRING   -> serialize_asn1_bit_string_TLV
  | OID          -> admit ()

#push-options "--query_stats --z3rlimit 32"
let safe_add
  (a b: option asn1_int32)
: Tot (c: option asn1_int32 {
          Some?a /\ Some?b /\ Some? c ==>
            v (Some?.v c) == v (Some?.v a) + v (Some?.v b)
  })
= let open FStar.Integers in
  if (Some?a && Some? b && (Some?.v a) <= asn1_int32_max - (Some?.v b)) then
  ( Some (Some?.v a + Some?.v b) )
  else
  ( None )
#pop-options

/// Length Spec of ASN.1 [VALUE] of primitive types
///
#push-options "--query_stats --z3rlimit 8"
noextract
let length_of_asn1_primitive_value
  (#_a: asn1_primitive_type)
  (value: datatype_of_asn1_type _a)
: GTot (length: asn1_length_of_type _a {
  length == Seq.length (
    match _a with
    | BOOLEAN      -> serialize serialize_asn1_boolean value
    | NULL         -> serialize serialize_asn1_null value
    | INTEGER      -> serialize (serialize_asn1_integer (length_of_asn1_integer (value <: datatype_of_asn1_type INTEGER))) value
    | OCTET_STRING -> serialize (serialize_asn1_octet_string (v (dfst (value <: datatype_of_asn1_type OCTET_STRING)))) value
    | BIT_STRING   -> serialize (serialize_asn1_bit_string (v (Mkdtuple3?._1 (value <: datatype_of_asn1_type BIT_STRING)))) value
    | OID          -> admit ())
  })
= match _a with
  | BOOLEAN      -> ( let value = value <: datatype_of_asn1_type BOOLEAN in
                      serialize_asn1_boolean_size value
                    ; 1 )

  | NULL         -> ( let value = value <: datatype_of_asn1_type NULL in
                      serialize_asn1_null_size value
                    ; 0 )

  | INTEGER      -> ( let value = value <: datatype_of_asn1_type INTEGER in
                      let length = length_of_asn1_integer value in
                      serialize_asn1_integer_size length value
                    ; length )

  | OCTET_STRING -> ( let value = value <: datatype_of_asn1_type OCTET_STRING in
                      let length = v (dfst value) in
                      serialize_asn1_octet_string_size length value
                    ; length )

  | BIT_STRING   -> ( let value = value <: datatype_of_asn1_type BIT_STRING in
                      let length = v (Mkdtuple3?._1 value) in
                      serialize_asn1_bit_string_size length value
                    ; length )

  | OID          -> admit ()
#pop-options

(* TODO: Revise this. *)
noextract
let asn1_length_inbound_of_primitive_value
  (#_a: asn1_primitive_type)
  (value: datatype_of_asn1_type _a)
: GTot (b: bool { b == asn1_length_inbound_of_type _a (length_of_asn1_primitive_value value) })
= let min, max = asn1_length_bound_of_type _a in
  let length = length_of_asn1_primitive_value value in
  asn1_length_inbound length min max

/// Length Spec of ASN.1 Primitive [TAG, LEN, VALUE] of primitive types
///
#push-options "--query_stats --z3rlimit 8"
noextract
let length_of_asn1_primitive_TLV
  (#_a: asn1_primitive_type)
  (value: datatype_of_asn1_type _a)
: GTot (length: nat { length == Seq.length (serialize (serialize_asn1_TLV_of_type _a) value) })
= match _a with
  | BOOLEAN      -> ( let value = value <: datatype_of_asn1_type BOOLEAN in
                      serialize_asn1_boolean_TLV_size value
                    ; 3 )

  | NULL         -> ( let value = value <: datatype_of_asn1_type NULL in
                      serialize_asn1_null_TLV_size value
                    ; 2 )

  | INTEGER      -> ( let value = value <: datatype_of_asn1_type INTEGER in
                      let length = length_of_asn1_integer value in
                      let len: asn1_int32_of_type INTEGER = u length in
                      serialize_asn1_integer_TLV_size value
                    ; 1 + length_of_asn1_length len + length )

  | OCTET_STRING -> ( let value = value <: datatype_of_asn1_type OCTET_STRING in
                      let length = v (dfst value) in
                      let len: asn1_int32_of_type OCTET_STRING = u length in
                      serialize_asn1_octet_string_TLV_size value
                    ; 1 + length_of_asn1_length len + length )

  | BIT_STRING   -> ( let value = value <: datatype_of_asn1_type BIT_STRING in
                      let length = v (Mkdtuple3?._1 value) in
                      let len: asn1_int32_of_type BIT_STRING = u length in
                      serialize_asn1_bit_string_TLV_size value
                    ; 1 + length_of_asn1_length len + length )

  | OID          -> admit ()
#pop-options

(* TODO: Revise this*)
noextract
let asn1_length_inbound_of_primitive_TLV
  (#_a: asn1_primitive_type)
  (value: datatype_of_asn1_type _a)
: GTot (bool)
= let min, max = asn1_length_bound_of_type _a in
  let length = length_of_asn1_primitive_TLV value in
  asn1_length_inbound length asn1_length_min asn1_length_max
