module ASN1.Low.Value.BigInteger

open ASN1.Base
open ASN1.Low.Base
open ASN1.Low.Tag
open ASN1.Low.Length
open ASN1.Low.Bytes32
open ASN1.Low.Value.OCTET_STRING
open ASN1.Spec.Value.BigInteger
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module MB = LowStar.Monotonic.Buffer
module B = LowStar.Buffer
module Cast = FStar.Int.Cast
open LowParse.Low.Bytes

open FStar.Integers
module B32 = FStar.Bytes

let serialize32_asn1_length_of_big_integer_backwards
: serializer32_backwards (serialize_asn1_length_of_big_integer)
= serialize32_asn1_length_of_bound_backwards 1ul (asn1_int32_max - 6ul)
  `coerce_serializer32_backwards _`
  (assert_norm (bounded_int32 1 (asn1_length_max - 6) == asn1_value_int32_of_big_integer))

inline_for_extraction
val serialize32_big_integer_as_octet_string_backwards
  (len: asn1_value_int32_of_big_integer)
: Tot (serializer32_backwards (serialize_big_integer_as_octet_string len))

noextract inline_for_extraction
let parser_tag_of_big_integer_as_octet_string_impl
  (x: big_integer_as_octet_string_t)
: Tot (tg: (the_asn1_tag INTEGER & asn1_value_int32_of_big_integer)
           { tg == parser_tag_of_big_integer_as_octet_string x })
= let (.[]) = B32.index in
  if ((x.s).[0] >= 0x80uy) then
  ( (INTEGER, x.ASN1.Base.len + 1ul) )
  else
  ( (INTEGER, x.ASN1.Base.len) )

val serialize32_big_integer_as_octet_string_TLV_backwards (_:unit)
: Tot (serializer32_backwards (serialize_big_integer_as_octet_string_TLV))
