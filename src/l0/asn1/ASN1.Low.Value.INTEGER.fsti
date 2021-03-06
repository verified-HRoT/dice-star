module ASN1.Low.Value.INTEGER

open ASN1.Base
open ASN1.Spec.Value.INTEGER
open ASN1.Low.Base

open FStar.Integers

(* NOTE: Read after `ASN1.Spec.Tag`, `ASN1.Spec.Length` *)

/// Implementation of length computation of `INTEGER` value's serialization
//inline_for_extraction
let len_of_asn1_integer
  (value: datatype_of_asn1_type INTEGER)
: (len: asn1_value_int32_of_type INTEGER { v len == length_of_asn1_integer value } )
= if      0l         <= value && value <= 0x7Fl      then
  ( 1ul )
  else if 0x7Fl       < value && value <= 0xFFl       then
  ( 2ul )
  else if 0xFFl       < value && value <= 0x7FFFl     then
  ( 2ul )
  else if 0x7FFFl     < value && value <= 0xFFFFl     then
  ( 3ul )
  else if 0xFFFFl     < value && value <= 0x7FFFFFl   then
  ( 3ul )
  else if 0x7FFFFFl   < value && value <= 0xFFFFFFl   then
  ( 4ul )
  else // if 0xFFFFFFl   < value && value <= 0x7FFFFFFFl then
  ( 4ul )

inline_for_extraction
val serialize32_asn1_integer_backwards
  (len: asn1_value_int32_of_type INTEGER)
: Tot (serializer32_backwards (serialize_asn1_integer (v len)))

inline_for_extraction
val parser_tag_of_asn1_integer_impl
  (value: datatype_of_asn1_type INTEGER)
: Tot (tg: (the_asn1_tag INTEGER & asn1_value_int32_of_type INTEGER) {
           tg == parser_tag_of_asn1_integer value
  })

inline_for_extraction
val synth_asn1_integer_V_inverse_impl
  (tag: (the_asn1_tag INTEGER & asn1_value_int32_of_type INTEGER))
  (value': refine_with_tag parser_tag_of_asn1_integer tag)
: Tot (value: datatype_of_asn1_type INTEGER {
               v (snd tag) == length_of_asn1_integer value /\
               value' == synth_asn1_integer_V tag value /\
               value == synth_asn1_integer_V_inverse tag value' })

// inline_for_extraction
val serialize32_asn1_integer_TLV_backwards (_:unit)
: Tot (serializer32_backwards (serialize_asn1_integer_TLV))
