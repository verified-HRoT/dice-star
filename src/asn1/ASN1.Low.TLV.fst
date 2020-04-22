module ASN1.Low.TLV

open ASN1.Base

open ASN1.Spec.Tag
open ASN1.Spec.Length
open ASN1.Spec.BOOLEAN
open ASN1.Spec.NULL
open ASN1.Spec.INTEGER
open ASN1.Spec.OCTET_STRING
open ASN1.Spec.BIT_STRING
open ASN1.Spec.SEQUENCE
open ASN1.Spec.TLV

open LowParse.Low.Base
open LowParse.Low.Combinators

open ASN1.Low.Base
open ASN1.Low.Tag
open ASN1.Low.Length
open ASN1.Low.BOOLEAN
open ASN1.Low.NULL
open ASN1.Low.INTEGER
open ASN1.Low.OCTET_STRING
open ASN1.Low.BIT_STRING
open ASN1.Low.SEQUENCE

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module MB = LowStar.Monotonic.Buffer
module B = LowStar.Buffer
module Cast = FStar.Int.Cast

open FStar.Integers

/// Len Impl of ASN.1 [VALUE] of primitive types
///
#push-options "--z3rlimit 16"
let len_of_asn1_primitive_value
  (#_a: asn1_primitive_type)
  (value: datatype_of_asn1_type _a)
: Tot (len: asn1_int32_of_type _a { v len == length_of_asn1_primitive_value value })
= match _a with
  | BOOLEAN      -> ( 1ul )

  | NULL         -> ( 0ul )

  | INTEGER      -> ( let value = value <: datatype_of_asn1_type INTEGER in
                      len_of_asn1_integer value )

  | OCTET_STRING -> ( let value = value <: datatype_of_asn1_type OCTET_STRING in
                      dfst value )

  | BIT_STRING   -> ( let value = value <: datatype_of_asn1_type BIT_STRING in
                      Mkdtuple3?._1 value )

  | OID          -> admit ()
#pop-options


/// Length Spec of ASN.1 Primitive [TAG, LEN, VALUE] of primitive types
///
#push-options "--query_stats --z3rlimit 64"
let len_of_asn1_primitive_TLV_unbounded
  (#_a: asn1_primitive_type)
  (value: datatype_of_asn1_type _a)
: Tot (len: option asn1_int32 {
         Some? len ==>
           (v (Some?.v len) == length_of_asn1_primitive_TLV value)
  })
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
  (* Prf *) assert (v value_len == length_of_asn1_primitive_value value);

  let len_len = len_of_asn1_length value_len in

  let tag_len = 1ul in

  (* Prf *) assert (v tag_len + v len_len + v value_len == Seq.length (serialize (serialize_asn1_TLV_of_type _a) value));

(* return *) Some tag_len `safe_add` Some len_len `safe_add` Some value_len
#pop-options

#push-options "--query_stats --z3rlimit 32"
let len_of_asn1_primitive_TLV_inbound
  (#_a: asn1_primitive_type)
  (value: datatype_of_asn1_type _a {
    asn1_length_inbound (length_of_asn1_primitive_TLV value) asn1_length_min asn1_length_max
  })
: Tot (len: asn1_int32 { v len == length_of_asn1_primitive_TLV value })
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

let valid_sequence_value_of
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
= x: t{ asn1_length_inbound_of_type SEQUENCE (Seq.length (serialize s x)) }

let valid_sequence_len_of
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (x: t)
= len: asn1_int32_of_type SEQUENCE { v len == Seq.length (serialize s x) }
