module ASN1.Spec.ANY

open LowParse.Spec.Base
open LowParse.Spec.Combinators

open ASN1.Base
open ASN1.Spec

open FStar.Integers

type asn1_value =
| BOOLEAN_VALUE      of datatype_of_asn1_type BOOLEAN
| NULL_VALUE         of datatype_of_asn1_type NULL
| INTEGER_VALUE      of datatype_of_asn1_type INTEGER
| OCTET_STRING_VALUE of datatype_of_asn1_type OCTET_STRING
| BIT_STRING_VALUE   of datatype_of_asn1_type BIT_STRING
| OID_VALUE          of datatype_of_asn1_type OID
| SEQUENCE_VALUE     of list asn1_value

let asn1_value_of_type
  (_a: asn1_type)
= match _a with
  | BOOLEAN      -> ( v: asn1_value {BOOLEAN_VALUE?      v} )
  | NULL         -> ( v: asn1_value {NULL_VALUE?         v} )
  | INTEGER      -> ( v: asn1_value {INTEGER_VALUE?      v} )
  | OCTET_STRING -> ( v: asn1_value {OCTET_STRING_VALUE? v} )
  | BIT_STRING   -> ( v: asn1_value {BIT_STRING_VALUE?   v} )
  | OID          -> ( v: asn1_value {OID_VALUE?          v} )
  | SEQUENCE     -> ( v: asn1_value {SEQUENCE_VALUE?     v} )

noextract
let synth_asn1_value_of_type
  (_a: asn1_primitive_type)
  (value: datatype_of_asn1_type _a)
: GTot (asn1_value_of_type _a)
= match _a with
  | BOOLEAN      -> ( BOOLEAN_VALUE      value )
  | NULL         -> ( NULL_VALUE         value )
  | INTEGER      -> ( INTEGER_VALUE      value )
  | OCTET_STRING -> ( OCTET_STRING_VALUE value )
  | BIT_STRING   -> ( BIT_STRING_VALUE   value )
  | OID          -> ( OID_VALUE          value )

noextract
let synth_asn1_value_of_type_inverse
  (_a: asn1_primitive_type)
  (value: asn1_value_of_type _a)
: GTot (datatype_of_asn1_type _a)
= match _a, value with
  | BOOLEAN     , BOOLEAN_VALUE      value -> value
  | NULL        , NULL_VALUE         value -> value
  | INTEGER     , INTEGER_VALUE      value -> value
  | OCTET_STRING, OCTET_STRING_VALUE value -> value
  | BIT_STRING  , BIT_STRING_VALUE   value -> value
  | OID         , OID_VALUE          value -> value

#push-options "--z3rlimit 32"
noextract
let parse_asn1_value_of_type
  (_a: asn1_primitive_type)
: parser (parse_asn1_TLV_kind_of_type _a) (asn1_value_of_type _a)
= match _a with
  | BOOLEAN      -> ( parse_asn1_boolean_TLV
                      `parse_synth`
                      synth_asn1_value_of_type _a )
  | NULL         -> ( parse_asn1_null_TLV
                      `parse_synth`
                      synth_asn1_value_of_type _a )
  | INTEGER      -> ( parse_asn1_integer_TLV
                      `parse_synth`
                      (*FIXME: Why only this one won't pass type check? *)
                      // synth_asn1_value_of_type _a )
                      (fun value -> INTEGER_VALUE value <: asn1_value_of_type _a) )
  | OCTET_STRING -> ( parse_asn1_octet_string_TLV
                      `parse_synth`
                      synth_asn1_value_of_type _a )
  | BIT_STRING   -> ( parse_asn1_bit_string_TLV
                      `parse_synth`
                      synth_asn1_value_of_type _a )
  | OID          -> ( admit () )

// noextract
// let serialize_asn1_value_of_type
//   (_a: asn1_primitive_type)
// : serializer (parse_asn1_value_of_type _a)
// = match _a with
//   | BOOLEAN      -> ( serialize_synth )
//   // | NULL         -> ( parse_asn1_null_TLV
//   //                     `parse_synth`
//   //                     synth_asn1_value_of_type _a )
//   // | INTEGER      -> ( parse_asn1_integer_TLV
//   //                     `parse_synth`
//   //                     (fun value -> INTEGER_VALUE value <: asn1_value_of_type _a) )
//   // | OCTET_STRING -> ( parse_asn1_octet_string_TLV
//   //                     `parse_synth`
//   //                     synth_asn1_value_of_type _a )
//   // | BIT_STRING   -> ( parse_asn1_bit_string_TLV
//   //                     `parse_synth`
//   //                     synth_asn1_value_of_type _a )
//   | OID          -> ( admit () )

// #push-options "--query_stats"
// let parse_any
// (* FIXME: Need a inductively defined datatype. *)
// = (parse_asn1_tag
//    `nondep_then`
//    parse_asn1_length)
//    `parse_filter`
//    (fun x -> fst x <> SEQUENCE &&
//            asn1_value_length_inbound_of_type (fst x) (v (snd x)))
//    `parse_synth`
//    (fun x -> (|fst x, snd x|) <: (tag: asn1_primitive_type & asn1_value_int32_of_type tag) )
//    `and_then`
//    (fun x -> match dfst x with
//            | BOOLEAN      -> ( parse_asn1_boolean                   )
//            | NULL         -> ( parse_asn1_null                      )
//            | INTEGER      -> ( parse_asn1_integer      (v (dsnd x)) )
//            | OCTET_STRING -> ( parse_asn1_octet_string (v (dsnd x)) )
//            | BIT_STRING   -> ( parse_asn1_bit_string   (v (dsnd x)) )
//            | OID          -> ( admit ()                             ) )
