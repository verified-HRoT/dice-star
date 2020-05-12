module ASN1.Low.TLV

open ASN1.Base

open ASN1.Spec.Tag
open ASN1.Spec.Length
open ASN1.Spec.Value.BOOLEAN
open ASN1.Spec.Value.NULL
open ASN1.Spec.Value.INTEGER
open ASN1.Spec.Value.OCTET_STRING
open ASN1.Spec.Value.BIT_STRING
open ASN1.Spec.Value.SEQUENCE
open ASN1.Spec.TLV

open LowParse.Low.Base
open LowParse.Low.Combinators

open ASN1.Low.Base
open ASN1.Low.Tag
open ASN1.Low.Length
open ASN1.Low.Value.BOOLEAN
open ASN1.Low.Value.NULL
open ASN1.Low.Value.INTEGER
open ASN1.Low.Value.OCTET_STRING
open ASN1.Low.Value.BIT_STRING
open ASN1.Low.Value.SEQUENCE

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module MB = LowStar.Monotonic.Buffer
module B = LowStar.Buffer
module Cast = FStar.Int.Cast

open FStar.Integers

(* NOTE: Read after `ASN1.Low.Tag`, `ASN1.Low.Length`, `ASN1.Low.Value.*` *)

/// Len Impl of ASN.1 [VALUE] of primitive types
///
#push-options "--z3rlimit 16"
let len_of_asn1_primitive_value
  (#_a: asn1_primitive_type)
  (value: datatype_of_asn1_type _a)
: Tot (len: asn1_value_int32_of_type _a { v len == length_of_asn1_primitive_value value })
= match _a with
  | BOOLEAN      -> ( 1ul )

  | NULL         -> ( 0ul )

  | INTEGER      -> ( let value = value <: datatype_of_asn1_type INTEGER in
                      len_of_asn1_integer value )

  | OCTET_STRING -> ( let value = value <: datatype_of_asn1_type OCTET_STRING in
                      dfst value )

  | BIT_STRING   -> ( let value = value <: datatype_of_asn1_type BIT_STRING in
                      Mkbit_string_t?.len value )

  | OID          -> admit ()
#pop-options


/// Length Spec of ASN.1 Primitive [TAG, LEN, VALUE] of primitive types
/// NOTE: Had updated the length range of ASN1 values to make all TLVs of
///       valid values are inbound. Maybe remove these `_unbounded` funcitons.
///
// #push-options "--z3rlimit 64"
// let len_of_asn1_primitive_TLV_unbounded
//   (#_a: asn1_primitive_type)
//   (value: datatype_of_asn1_type _a)
// : Tot (len: option asn1_int32 {
//          Some? len ==>
//            (v (Some?.v len) == length_of_asn1_primitive_TLV value)
//   })
// = (* Prf *) ( match _a with
//               | BOOLEAN      -> ( serialize_asn1_boolean_TLV_size        (value <: datatype_of_asn1_type BOOLEAN     )
//                                 ; serialize_asn1_boolean_TLV_unfold      (value <: datatype_of_asn1_type BOOLEAN     ) )
//               | NULL         -> ( serialize_asn1_null_TLV_size           (value <: datatype_of_asn1_type NULL        )
//                                 ; serialize_asn1_null_TLV_unfold         (value <: datatype_of_asn1_type NULL        ) )
//               | INTEGER      -> ( serialize_asn1_integer_TLV_size        (value <: datatype_of_asn1_type INTEGER     )
//                                 ; serialize_asn1_integer_TLV_unfold      (value <: datatype_of_asn1_type INTEGER     ) )
//               | OCTET_STRING -> ( serialize_asn1_octet_string_TLV_size   (value <: datatype_of_asn1_type OCTET_STRING)
//                                 ; serialize_asn1_octet_string_TLV_unfold (value <: datatype_of_asn1_type OCTET_STRING) )
//               | BIT_STRING   -> ( serialize_asn1_bit_string_TLV_size     (value <: datatype_of_asn1_type BIT_STRING  )
//                                 ; serialize_asn1_bit_string_TLV_unfold   (value <: datatype_of_asn1_type BIT_STRING  ) )
//               | OID          -> ( admit() ) );

//   let value_len = len_of_asn1_primitive_value value in
//   (* Prf *) assert (v value_len == length_of_asn1_primitive_value value);

//   let len_len = len_of_asn1_length value_len in

//   let tag_len = 1ul in

//   (* Prf *) assert (v tag_len + v len_len + v value_len == Seq.length (serialize (serialize_asn1_TLV_of_type _a) value));

// (* return *) Some tag_len `safe_add` Some len_len `safe_add` Some value_len
// #pop-options


#push-options "--z3rlimit 32"
let len_of_asn1_primitive_TLV
  (#_a: asn1_primitive_type)
  (value: datatype_of_asn1_type _a)
: Tot (len: asn1_TLV_int32_of_type _a { v len == length_of_asn1_primitive_TLV value })
= (* Prf *) ( match _a with
              | BOOLEAN      -> ( serialize_asn1_boolean_TLV_size        (value <: datatype_of_asn1_type BOOLEAN     )
                                ; serialize_asn1_boolean_TLV_unfold      (value <: datatype_of_asn1_type BOOLEAN     ) )
              | NULL         -> ( serialize_asn1_null_TLV_size           (value <: datatype_of_asn1_type NULL        )
                                ; serialize_asn1_null_TLV_unfold         (value <: datatype_of_asn1_type NULL        ) )
              | INTEGER      -> ( serialize_asn1_integer_TLV_size        (value <: datatype_of_asn1_type INTEGER     )
                                ; serialize_asn1_integer_TLV_unfold      (value <: datatype_of_asn1_type INTEGER     ) )
              | OCTET_STRING -> ( serialize_asn1_octet_string_TLV_size   (value <: datatype_of_asn1_type OCTET_STRING)
                                ; serialize_asn1_octet_string_TLV_unfold (value <: datatype_of_asn1_type OCTET_STRING) )
              | BIT_STRING   -> ( serialize_asn1_bit_string_TLV_size     (value <: datatype_of_asn1_type BIT_STRING  )
                                ; serialize_asn1_bit_string_TLV_unfold   (value <: datatype_of_asn1_type BIT_STRING  ) )
              | OID          -> ( admit() ) );

  let value_len = len_of_asn1_primitive_value value in

  let len_len = len_of_asn1_length value_len in

  let tag_len = 1ul in

(* return *) tag_len + len_len + value_len
#pop-options

/// Interfaces
///
inline_for_extraction noextract
let serialize32_asn1_TLV_backwards_of_type
  (_a: asn1_primitive_type)
: serializer32_backwards (serialize_asn1_TLV_of_type _a)
= match _a with
  | BOOLEAN      -> serialize32_asn1_boolean_TLV_backwards      ()
  | NULL         -> serialize32_asn1_null_TLV_backwards         ()
  | INTEGER      -> serialize32_asn1_integer_TLV_backwards      ()
  | OCTET_STRING -> serialize32_asn1_octet_string_TLV_backwards ()
  | BIT_STRING   -> serialize32_asn1_bit_string_TLV_backwards   ()
  | OID          -> admit ()


/// type of a valid (inbound) sequence value
///
let inbound_sequence_value_of
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
= x: t{ asn1_value_length_inbound_of_type SEQUENCE (Seq.length (serialize s x)) }

/// type of a valid sequence value's len
let inbound_sequence_value_len_of
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (x: t)
= len: asn1_value_int32_of_type SEQUENCE { v len == Seq.length (serialize s x) }
