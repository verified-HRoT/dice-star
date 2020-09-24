module ASN1.Spec.Value.BigInteger

open ASN1.Spec.Base
open LowParse.Spec.SeqBytes.Base

open ASN1.Base
open ASN1.Spec.Tag
open ASN1.Spec.Length

open FStar.Integers

module B32 = FStar.Bytes

unfold
let big_integer_as_octet_string_t
= x: datatype_of_asn1_type OCTET_STRING
  { let (.[]) = B32.index in
    v (dfst x) > 0 /\                      // no nil
    ( if (v (dfst x) > 1) then
      ( (dsnd x).[0] =!= 0x00uy )  // no leading zero byte if length > 1
      else ( True ) ) /\
    ( if ((dsnd x).[0] >= 0x80uy) then   // leave one space for leading zero byte
      ( v (dfst x) <= asn1_length_max - 7 )
      else ( True ) ) }

let asn1_value_length_of_big_integer
= l: asn1_length_t { 1 <= l /\ l <= asn1_length_max - 6}

unfold
let valid_big_integer_as_octet_string_prop
  (l: asn1_value_length_of_big_integer)
  (x: big_integer_as_octet_string_t)
: Type0
= v (dfst x) > 0 /\
  ( let (.[]) = B32.index in
    if l = 1 then
    ( v (dfst x) == l /\ (dsnd x).[0] < 0x80uy )
    else if ((dsnd x).[0] >= 0x80uy) then
    ( v (dfst x) == l - 1 )
    else
    ( v (dfst x) == l /\ (dsnd x).[0] > 0x00uy ) )

let parse_big_integer_as_octet_string_kind (l: asn1_value_length_of_big_integer) = constant_size_parser_kind l

val parse_big_integer_as_octet_string
  (l: asn1_value_length_of_big_integer)
: parser (parse_big_integer_as_octet_string_kind l) (x: big_integer_as_octet_string_t {valid_big_integer_as_octet_string_prop l x})

val serialize_big_integer_as_octet_string
  (l: asn1_value_length_of_big_integer)
: serializer (parse_big_integer_as_octet_string l)

// val lemma_serialize_big_integer_as_octet_string_unfold
//   (l: asn1_value_length_of_big_integer)
//   (value: get_parser_type (parse_big_integer_as_octet_string l))
// : Lemma (
//   serialize (serialize_big_integer_as_octet_string l) value ==
//   serialize (serialize_seq_flbytes l) (synth_big_integer_as_octet_string_inverse l value))

val lemma_serialize_big_integer_as_octet_string_size
  (l: asn1_value_length_of_big_integer)
  (value: get_parser_type (parse_big_integer_as_octet_string l))
: Lemma (
  Seq.length (serialize (serialize_big_integer_as_octet_string l) value) == l)
