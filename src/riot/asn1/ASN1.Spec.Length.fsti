module ASN1.Spec.Length

open ASN1.Spec.Base
open LowParse.Spec.DER
open ASN1.Base

module U8  = FStar.UInt8
module U32 = FStar.UInt32
module Cast = FStar.Int.Cast

#set-options "--z3rlimit 32 --fuel 0 --ifuel 0"

/// ASN1 length parser, based on `LowParse.Spec.DER`

/// Generic
///

inline_for_extraction noextract
let parse_asn1_length_of_bound_kind
  (min: asn1_length_t)
  (max: asn1_length_t { min <= max })
: parser_kind
= parse_bounded_der_length32_kind min max

val parse_asn1_length_of_bound
  (min: asn1_length_t)
  (max: asn1_length_t { min <= max })
: parser (parse_asn1_length_of_bound_kind min max) (bounded_int32 min max)

val serialize_asn1_length_of_bound
  (min: asn1_length_t)
  (max: asn1_length_t { min <= max })
: serializer (parse_asn1_length_of_bound min max)

val lemma_serialize_asn1_length_of_bound_unfold
  (min: asn1_length_t)
  (max: asn1_length_t { min <= max })
  (y': bounded_int32 min max)
: Lemma (
    let res = serialize_asn1_length_of_bound min max `serialize` y' in
    let x = tag_of_der_length32_impl y' in
    let s1 = Seq.create 1 x in
    if x `U8.lt` 128uy
    then res `Seq.equal` s1
    else if x = 129uy
    then U32.v y' <= 255 /\ res `Seq.equal` (s1 `Seq.append` Seq.create 1 (Cast.uint32_to_uint8 y'))
    else
      let len = log256' (U32.v y') in
      res `Seq.equal` (s1 `Seq.append` serialize (serialize_bounded_integer len) y')
)

val lemma_serialize_asn1_length_of_bound_size
  (min: asn1_length_t)
  (max: asn1_length_t { min <= max })
  (y': bounded_int32 min max)
: Lemma
  (
    Seq.length (serialize (serialize_asn1_length_of_bound min max) y') == (
      if y' `U32.lt` 128ul
      then 1
      else if y' `U32.lt` 256ul
      then 2
      else if y' `U32.lt` 65536ul
      then 3
      else if y' `U32.lt` 16777216ul
      then 4
      else 5
 ))

inline_for_extraction noextract
let parse_asn1_length_kind = parse_asn1_length_of_bound_kind asn1_length_min asn1_length_max

let parse_asn1_length
: parser parse_asn1_length_kind asn1_int32
= parse_asn1_length_of_bound asn1_length_min asn1_length_max

let serialize_asn1_length
: serializer parse_asn1_length
= serialize_asn1_length_of_bound asn1_length_min asn1_length_max

let lemma_serialize_asn1_length_unfold
= lemma_serialize_asn1_length_of_bound_unfold asn1_length_min asn1_length_max

let lemma_serialize_asn1_length_size
= lemma_serialize_asn1_length_of_bound_size asn1_length_min asn1_length_max

(* Considering to expose this definition. *)
val length_of_asn1_length
  (len: asn1_int32)
: GTot (length: asn1_length_t
       { length == Seq.length (serialize serialize_asn1_length len) /\
         length <= 5 })
// = lemma_serialize_asn1_length_unfold len;
//   lemma_serialize_asn1_length_size len;
//   let x = tag_of_der_length32 len in
//   let open FStar.Integers in
//   if x < 128uy then
//   ( 1 )
//   else if x = 129uy then
//   ( 2 )
//   else if x = 130uy then
//   ( 3 )
//   else if x = 131uy then
//   ( 4 )
//   else
//   ( 5 )

/// Specialized for a specific ASN1 type
///

inline_for_extraction noextract
let parse_asn1_length_kind_of_type
  (_a: asn1_tag_t)
: parser_kind
= parse_bounded_der_length32_kind (asn1_value_length_min_of_type _a) (asn1_value_length_max_of_type _a)

let parse_asn1_length_of_type
  (_a: asn1_tag_t)
: parser (parse_asn1_length_kind_of_type _a) (asn1_value_int32_of_type _a)
= parse_asn1_length_of_bound (asn1_value_length_min_of_type _a) (asn1_value_length_max_of_type _a)

let serialize_asn1_length_of_type
  (_a: asn1_tag_t)
: serializer (parse_asn1_length_of_type _a)
= serialize_asn1_length_of_bound (asn1_value_length_min_of_type _a) (asn1_value_length_max_of_type _a)

let lemma_serialize_asn1_length_of_type_unfold
  (_a: asn1_tag_t)
= lemma_serialize_asn1_length_of_bound_unfold (asn1_value_length_min_of_type _a) (asn1_value_length_max_of_type _a)

let lemma_serialize_asn1_length_of_type_size
  (_a: asn1_tag_t)
= lemma_serialize_asn1_length_of_bound_size (asn1_value_length_min_of_type _a) (asn1_value_length_max_of_type _a)

val serialize_asn1_length_of_bound_eq
  (min: asn1_length_t)
  (max: asn1_length_t { min <= max })
  (len: bounded_int32 min max)
: Lemma (
  serialize serialize_asn1_length len ==
  serialize (serialize_asn1_length_of_bound min max) len
)

val serialize_asn1_length_of_type_eq
  (_a: asn1_tag_t)
  (len: asn1_value_int32_of_type _a)
: Lemma (
  serialize serialize_asn1_length len ==
  serialize (serialize_asn1_length_of_type _a) len
)
