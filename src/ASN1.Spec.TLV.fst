module ASN1.Spec.TLV

open ASN1.Spec.Base

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
open LowParse.Bytes

open FStar.Integers

(* NOTE: Read after `ASN1.Spec.Tag`, `ASN1.Spec.Length`, `ASN1.Spec.Value.*` *)

/// Interfaces to make this library easier to use, WIP
///
inline_for_extraction noextract
let parse_asn1_TLV_kind_of_type
  (_a: asn1_primitive_type)
: parser_kind
= match _a with
  | BOOLEAN      -> parse_asn1_boolean_TLV_kind
  | NULL         -> parse_asn1_null_TLV_kind
  | INTEGER      -> parse_asn1_integer_TLV_kind
  | OCTET_STRING -> parse_asn1_octet_string_TLV_kind
  | BIT_STRING   -> parse_asn1_bit_string_TLV_kind
  | OID          -> parse_asn1_oid_TLV_kind

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
  | OID          -> parse_asn1_oid_TLV

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
  | OID          -> serialize_asn1_oid_TLV

/// Length Spec of ASN.1 [VALUE] of primitive types
///
#push-options "--z3rlimit 8"
noextract
let length_of_asn1_primitive_value
  (#_a: asn1_primitive_type)
  (value: datatype_of_asn1_type _a)
: GTot (length: asn1_value_length_of_type _a {
  length == Seq.length (
    match _a with
    | BOOLEAN      -> serialize serialize_asn1_boolean value
    | NULL         -> serialize serialize_asn1_null value
    | INTEGER      -> serialize (serialize_asn1_integer (length_of_asn1_integer (value <: datatype_of_asn1_type INTEGER))) value
    | OCTET_STRING -> serialize (serialize_asn1_octet_string (v (dfst (value <: datatype_of_asn1_type OCTET_STRING)))) value
    | BIT_STRING   -> serialize (serialize_asn1_bit_string (v (Mkbit_string_t?.bs_len (value <: datatype_of_asn1_type BIT_STRING)))) value
    | OID          -> serialize (serialize_asn1_oid (length_of_oid (value <: datatype_of_asn1_type OID))) value )
  })
= match _a with
  | BOOLEAN      -> ( let value = value <: datatype_of_asn1_type BOOLEAN in
                      lemma_serialize_asn1_boolean_size value
                    ; 1 )

  | NULL         -> ( let value = value <: datatype_of_asn1_type NULL in
                      lemma_serialize_asn1_null_size value
                    ; 0 )

  | INTEGER      -> ( let value = value <: datatype_of_asn1_type INTEGER in
                      let length = length_of_asn1_integer value in
                      lemma_serialize_asn1_integer_size length value
                    ; length )

  | OCTET_STRING -> ( let value = value <: datatype_of_asn1_type OCTET_STRING in
                      let length = v (dfst value) in
                      lemma_serialize_asn1_octet_string_size length value
                    ; length )

  | BIT_STRING   -> ( let value = value <: datatype_of_asn1_type BIT_STRING in
                      let length = v (Mkbit_string_t?.bs_len value) in
                      lemma_serialize_asn1_bit_string_size length value
                    ; length )

  | OID          -> ( let value = value <: datatype_of_asn1_type OID in
                      let length = length_of_oid value in
                      lemma_serialize_asn1_oid_size length value
                    ; length )
#pop-options

/// Length Spec of ASN.1 Primitive [TAG, LEN, VALUE] of primitive types
///
#push-options "--z3rlimit 32"
noextract
let length_of_asn1_primitive_TLV
  (#_a: asn1_primitive_type)
  (value: datatype_of_asn1_type _a)
: GTot (length: asn1_TLV_length_of_type _a {
               (* Provide proofs here *)
               let _ =
               (match _a with
                | BOOLEAN      -> ( let value = value <: datatype_of_asn1_type BOOLEAN in
                                    lemma_serialize_asn1_boolean_TLV_size value )

                | NULL         -> ( let value = value <: datatype_of_asn1_type NULL in
                                    lemma_serialize_asn1_null_TLV_size value )

                | INTEGER      -> ( let value = value <: datatype_of_asn1_type INTEGER in
                                    let length = length_of_asn1_integer value in
                                    let len: asn1_value_int32_of_type INTEGER = u length in
                                    lemma_serialize_asn1_integer_TLV_size value )

                | OCTET_STRING -> ( let value = value <: datatype_of_asn1_type OCTET_STRING in
                                    let length = v (dfst value) in
                                    let len: asn1_value_int32_of_type OCTET_STRING = u length in
                                    lemma_serialize_asn1_octet_string_TLV_size value )

                | BIT_STRING   -> ( let value = value <: datatype_of_asn1_type BIT_STRING in
                                    let length = v (Mkbit_string_t?.bs_len value) in
                                    let len: asn1_value_int32_of_type BIT_STRING = u length in
                                    lemma_serialize_asn1_bit_string_TLV_size value )

                | OID          -> ( let value = value <: datatype_of_asn1_type OID in
                                    let length = length_of_oid value in
                                    lemma_serialize_asn1_oid_size length value )) in
                length == Seq.length (serialize (serialize_asn1_TLV_of_type _a) value)
})
= match _a with
  | BOOLEAN      -> ( let value = value <: datatype_of_asn1_type BOOLEAN in
                      lemma_serialize_asn1_boolean_TLV_size value
                    ; 3 )

  | NULL         -> ( let value = value <: datatype_of_asn1_type NULL in
                      lemma_serialize_asn1_null_TLV_size value
                    ; 2 )

  | INTEGER      -> ( let value = value <: datatype_of_asn1_type INTEGER in
                      let length = length_of_asn1_integer value in
                      let len: asn1_value_int32_of_type INTEGER = u length in
                      lemma_serialize_asn1_integer_TLV_size value
                    ; 1 + length_of_asn1_length len + length )

  | OCTET_STRING -> ( let value = value <: datatype_of_asn1_type OCTET_STRING in
                      let length = v (dfst value) in
                      let len: asn1_value_int32_of_type OCTET_STRING = u length in
                      lemma_serialize_asn1_octet_string_TLV_size value
                    ; 1 + length_of_asn1_length len + length )

  | BIT_STRING   -> ( let value = value <: datatype_of_asn1_type BIT_STRING in
                      let length = v (Mkbit_string_t?.bs_len value) in
                      let len: asn1_value_int32_of_type BIT_STRING = u length in
                      lemma_serialize_asn1_bit_string_TLV_size value
                    ; 1 + length_of_asn1_length len + length )

  | OID          -> ( let value = value <: datatype_of_asn1_type OID in
                      let length = length_of_oid value in
                      let len: asn1_value_int32_of_type OID = u length in
                      lemma_serialize_asn1_oid_TLV_size value
                    ; 1 + length_of_asn1_length len + length )
#pop-options

unfold
let length_of_TLV
  (a: asn1_type)
  (l: asn1_value_length_of_type a)
: GTot (asn1_TLV_length_of_type a)
= 1 + length_of_asn1_length (u l) + l

let _ =
assert_norm (length_of_asn1_primitive_value (Mkbit_string_t 33ul 1ul (magic())) == 33)

#push-options "--z3rlimit 32"
let _ =
  lemma_serialize_asn1_oid_TLV_size OID_RIOT;
assert (length_of_asn1_primitive_TLV OID_RIOT == 11)
