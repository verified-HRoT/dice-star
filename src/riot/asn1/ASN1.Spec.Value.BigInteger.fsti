module ASN1.Spec.Value.BigInteger

open ASN1.Spec.Base
open LowParse.Spec.SeqBytes.Base

open ASN1.Base
open ASN1.Spec.Tag
open ASN1.Spec.Length
open LowParse.Spec.DER

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

let asn1_value_int32_of_big_integer
= LowParse.Spec.BoundedInt.bounded_int32 1 (asn1_length_max - 6)

let asn1_TLV_length_of_big_integer
= l: asn1_length_t { 3 <= l /\ l <= asn1_length_max }

let asn1_TLV_int32_of_big_integer
= LowParse.Spec.BoundedInt.bounded_int32 3 asn1_length_max

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

(* ZT: Exposing them because one lemma needs `synth_..._inverse`. *)
val filter_big_integer_as_octet_string
  (l: asn1_value_length_of_big_integer)
  (s: lbytes l)
: GTot bool

val synth_big_integer_as_octet_string
  (l: asn1_value_length_of_big_integer)
  (s: parse_filter_refine (filter_big_integer_as_octet_string l))
: GTot (value: big_integer_as_octet_string_t
               { valid_big_integer_as_octet_string_prop l value })

val lemma_synth_big_integer_as_octet_string_injective
  (l: asn1_value_length_of_big_integer)
: Lemma (
  synth_injective (synth_big_integer_as_octet_string l)
)

val synth_big_integer_as_octet_string_inverse
  (l: asn1_value_length_of_big_integer)
  (value: big_integer_as_octet_string_t {valid_big_integer_as_octet_string_prop l value})
: GTot (s32: parse_filter_refine (filter_big_integer_as_octet_string l)
            { value == synth_big_integer_as_octet_string l s32 })

let parse_big_integer_as_octet_string_kind (l: asn1_value_length_of_big_integer) = constant_size_parser_kind l

noextract
val parse_big_integer_as_octet_string
  (l: asn1_value_length_of_big_integer)
: parser (parse_big_integer_as_octet_string_kind l) (x: big_integer_as_octet_string_t {valid_big_integer_as_octet_string_prop l x})

noextract
val serialize_big_integer_as_octet_string
  (l: asn1_value_length_of_big_integer)
: serializer (parse_big_integer_as_octet_string l)

val lemma_serialize_big_integer_as_octet_string_unfold
  (l: asn1_value_length_of_big_integer)
  (value: get_parser_type (parse_big_integer_as_octet_string l))
: Lemma (
  serialize (serialize_big_integer_as_octet_string l) value ==
  serialize (serialize_seq_flbytes l) (synth_big_integer_as_octet_string_inverse l value))

val lemma_serialize_big_integer_as_octet_string_size
  (l: asn1_value_length_of_big_integer)
  (value: get_parser_type (parse_big_integer_as_octet_string l))
: Lemma (
  Seq.length (serialize (serialize_big_integer_as_octet_string l) value) == l)



let parser_tag_of_big_integer_as_octet_string
  (x: big_integer_as_octet_string_t)
: Tot (the_asn1_tag INTEGER & asn1_value_int32_of_big_integer)
= let (.[]) = B32.index in
  if ((dsnd x).[0] >= 0x80uy) then
  ( (INTEGER, dfst x + 1ul) )
  else
  ( (INTEGER, dfst x) )

let parse_asn1_length_kind_of_big_integer
= parse_bounded_der_length32_kind 1 (asn1_length_max - 6)

let parse_asn1_length_of_big_integer
: parser parse_asn1_length_kind_of_big_integer asn1_value_int32_of_big_integer
= parse_asn1_length_of_bound 1 (asn1_length_max - 6)

let serialize_asn1_length_of_big_integer
: serializer (parse_asn1_length_of_big_integer)
= serialize_asn1_length_of_bound 1 (asn1_length_max - 6)

let weak_kind_of_big_integer
= strong_parser_kind 1 (asn1_length_max - 6) None

inline_for_extraction noextract
let parse_big_integer_as_octet_string_TLV_kind
: parser_kind
= parse_asn1_tag_kind
  `and_then_kind`
  parse_asn1_length_kind_of_big_integer
  `and_then_kind`
  weak_kind_of_big_integer

noextract
val parse_big_integer_as_octet_string_TLV
: parser parse_big_integer_as_octet_string_TLV_kind big_integer_as_octet_string_t

noextract
val serialize_big_integer_as_octet_string_TLV
: serializer parse_big_integer_as_octet_string_TLV

val lemma_serialize_big_integer_as_octet_string_TLV_unfold
  (value: big_integer_as_octet_string_t)
: Lemma (
  let tg = parser_tag_of_big_integer_as_octet_string value in
  serialize serialize_big_integer_as_octet_string_TLV value ==
  serialize (serialize_asn1_tag_of_type INTEGER) INTEGER
  `Seq.append`
  serialize (serialize_asn1_length_of_big_integer) (snd tg)
  `Seq.append`
  serialize (serialize_big_integer_as_octet_string (v (snd tg))) value
)

let length_of_big_integer_as_octet_string
  (x: big_integer_as_octet_string_t)
: GTot (asn1_TLV_length_of_big_integer)
= let tg = parser_tag_of_big_integer_as_octet_string x in
  1 + length_of_asn1_length (snd tg) + v (snd tg)

let len_of_big_integer_as_octet_string
  (x: big_integer_as_octet_string_t)
: Tot (len: asn1_TLV_int32_of_big_integer
            { v len == length_of_big_integer_as_octet_string x })
= let tg = parser_tag_of_big_integer_as_octet_string x in
  1ul + ASN1.Low.Length.len_of_asn1_length (snd tg) + (snd tg)

val lemma_serialize_big_integer_as_octet_string_TLV_size
  (value: big_integer_as_octet_string_t)
: Lemma (
  Seq.length (serialize serialize_big_integer_as_octet_string_TLV value) ==
  length_of_big_integer_as_octet_string value
)
