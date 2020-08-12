module ASN1.Low.TLV

open ASN1.Base

open ASN1.Spec.Tag
open ASN1.Spec.Length
open ASN1.Spec.Value.BOOLEAN
open ASN1.Spec.Value.NULL
open ASN1.Spec.Value.INTEGER
open ASN1.Spec.Value.OCTET_STRING
open ASN1.Spec.Value.BIT_STRING
open ASN1.Spec.Value.OID
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
open ASN1.Low.Value.OID
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
inline_for_extraction noextract
let len_of_asn1_primitive_value
  (#_a: asn1_primitive_type)
  (value: datatype_of_asn1_type _a)
: Tot (len: asn1_value_int32_of_type _a { v len == length_of_asn1_primitive_value value })
= match _a with
  | BOOLEAN      -> ( 1ul )

  | ASN1_NULL         -> ( 0ul )

  | INTEGER      -> ( let value = value <: datatype_of_asn1_type INTEGER in
                      len_of_asn1_integer value )

  | OCTET_STRING -> ( let value = value <: datatype_of_asn1_type OCTET_STRING in
                      dfst value )

  | BIT_STRING   -> ( let value = value <: datatype_of_asn1_type BIT_STRING in
                      Mkbit_string_t?.bs_len value )

  | OID          -> ( let value = value <: datatype_of_asn1_type OID in
                      len_of_oid_buffer value )
#pop-options

#push-options "--z3rlimit 64"
inline_for_extraction noextract
let len_of_asn1_primitive_TLV
  (#_a: asn1_primitive_type)
  (value: datatype_of_asn1_type _a)
: Tot (len: asn1_TLV_int32_of_type _a { v len == length_of_asn1_primitive_TLV value })
= (* Prf *) ( match _a with
              | BOOLEAN      -> ( lemma_serialize_asn1_boolean_TLV_size        (value <: datatype_of_asn1_type BOOLEAN     )
                                ; lemma_serialize_asn1_boolean_TLV_unfold      (value <: datatype_of_asn1_type BOOLEAN     ) )
              | ASN1_NULL         -> ( lemma_serialize_asn1_ASN1_NULL_TLV_size           (value <: datatype_of_asn1_type ASN1_NULL        )
                                ; lemma_serialize_asn1_ASN1_NULL_TLV_unfold         (value <: datatype_of_asn1_type ASN1_NULL        ) )
              | INTEGER      -> ( lemma_serialize_asn1_integer_TLV_size        (value <: datatype_of_asn1_type INTEGER     )
                                ; lemma_serialize_asn1_integer_TLV_unfold      (value <: datatype_of_asn1_type INTEGER     ) )
              | OCTET_STRING -> ( lemma_serialize_asn1_octet_string_TLV_size   (value <: datatype_of_asn1_type OCTET_STRING)
                                ; lemma_serialize_asn1_octet_string_TLV_unfold (value <: datatype_of_asn1_type OCTET_STRING) )
              | BIT_STRING   -> ( lemma_serialize_asn1_bit_string_TLV_size     (value <: datatype_of_asn1_type BIT_STRING  )
                                ; lemma_serialize_asn1_bit_string_TLV_unfold   (value <: datatype_of_asn1_type BIT_STRING  ) )
              | OID          -> ( lemma_serialize_asn1_oid_TLV_size            (value <: datatype_of_asn1_type OID         )
                                ; lemma_serialize_asn1_oid_TLV_unfold          (value <: datatype_of_asn1_type OID         ) ) );

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
  | ASN1_NULL         -> serialize32_asn1_ASN1_NULL_TLV_backwards         ()
  | INTEGER      -> serialize32_asn1_integer_TLV_backwards      ()
  | OCTET_STRING -> serialize32_asn1_octet_string_TLV_backwards ()
  | BIT_STRING   -> serialize32_asn1_bit_string_TLV_backwards   ()
  | OID          -> serialize32_asn1_oid_TLV_backwards          ()

unfold
let len_of_TLV
  (a: asn1_tag_t)
  (len: asn1_value_int32_of_type a)
: Tot (out: asn1_TLV_int32_of_type a
            { v out == length_of_TLV a (v len) })
= 1ul + len_of_asn1_length len + len
