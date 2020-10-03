module ASN1.Low.Length
///
/// ASN.1 Low
///

open ASN1.Base
open ASN1.Spec.Length
open ASN1.Low.Base

module LDER = LowParse.Low.DER
module SDER = LowParse.Spec.DER

open FStar.Integers

#reset-options "--fuel 0 --ifuel 0"

let len_of_asn1_length
  (len: asn1_int32)
: (offset: size_t{v offset == Seq.length (serialize serialize_asn1_length len)})
= lemma_serialize_asn1_length_size len;
  let x = SDER.tag_of_der_length32_impl len in
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

#push-options "--z3rlimit 32"
inline_for_extraction
val serialize32_asn1_length (_:unit)
: (serializer32 serialize_asn1_length)

inline_for_extraction
val serialize32_asn1_length_backwards (_:unit)
: Tot (serializer32_backwards serialize_asn1_length)

inline_for_extraction noextract
val serialize32_asn1_length_of_type
  (_a: asn1_tag_t)
: (serializer32 (serialize_asn1_length_of_type _a))

inline_for_extraction noextract
val serialize32_asn1_length_of_bound_backwards
  (min: asn1_int32)
  (max: asn1_int32 { min <= max })
: (serializer32_backwards (serialize_asn1_length_of_bound (v min) (v max)))

//marking it noextract, perhaps issue because _a isn't fixed yet??
inline_for_extraction noextract
val serialize32_asn1_length_of_type_backwards
  (_a: asn1_tag_t)
: (serializer32_backwards (serialize_asn1_length_of_type _a))
#pop-options
