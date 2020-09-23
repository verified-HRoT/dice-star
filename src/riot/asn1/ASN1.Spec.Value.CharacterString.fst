module ASN1.Spec.Value.CharacterString

open ASN1.Spec.Base
open LowParse.Spec.Bytes

open ASN1.Base
open ASN1.Spec.Tag
open ASN1.Spec.Length
include ASN1.Spec.Value.StringCombinator
include ASN1.Spec.Value.IA5_STRING
include ASN1.Spec.Value.PRINTABLE_STRING

open FStar.Integers

module B32 = FStar.Bytes

#set-options "--z3rlimit 32 --fuel 0 --ifuel 0"

noextract inline_for_extraction
let len_of_character_string
  (t: character_string_type)
  (x: datatype_of_asn1_type t)
: Tot (asn1_value_int32_of_type t)
= match t with
  | IA5_STRING -> dfst (x <: datatype_of_asn1_type IA5_STRING)
  | PRINTABLE_STRING -> dfst (x <: datatype_of_asn1_type PRINTABLE_STRING)

let filter_character_string
  (t: character_string_type)
  (len: asn1_value_int32_of_type t)
  (s32: B32.lbytes32 len)
: GTot (bool)
= match t with
  | IA5_STRING -> filter_asn1_ia5_string len s32
  | PRINTABLE_STRING -> filter_asn1_printable_string len s32

let synth_character_string
  (t: character_string_type)
  (len: asn1_value_int32_of_type t)
  (s32: parse_filter_refine (filter_character_string t len))
: GTot (x: datatype_of_asn1_type t{ len_of_character_string t x == len })
= match t with
  | IA5_STRING -> synth_asn1_ia5_string len s32
  | PRINTABLE_STRING -> synth_asn1_printable_string len s32

noextract inline_for_extraction
let synth_character_string_inverse
  (t: character_string_type)
  (len: asn1_value_int32_of_type t)
  (x: datatype_of_asn1_type t{ len_of_character_string t x == len })
: Tot (s32: parse_filter_refine (filter_character_string t len)
            { x == synth_character_string t len s32 })
= match t with
  | IA5_STRING -> synth_asn1_ia5_string_inverse len x
  | PRINTABLE_STRING -> synth_asn1_printable_string_inverse len x

noextract
let string_prf
  (t: character_string_type)
= match t with
  | IA5_STRING -> ()
  | PRINTABLE_STRING -> ()

noextract inline_for_extraction
let count_character
  (t: character_string_type)
  (x: datatype_of_asn1_type t)
: Tot (asn1_int32)
= match t with
  | IA5_STRING -> count_ia5_character x
  | PRINTABLE_STRING -> count_printable_character x

let parse_asn1_character_string
  (t: character_string_type)
: parser (parse_asn1_string_TLV_kind t) (datatype_of_asn1_type t)
= match t with
  | IA5_STRING -> parse_asn1_ia5_string_TLV
  | PRINTABLE_STRING -> parse_asn1_printable_string_TLV

let serialize_asn1_character_string
  (t: character_string_type)
: serializer (parse_asn1_character_string t)
= match t with
  | IA5_STRING -> serialize_asn1_ia5_string_TLV
  | PRINTABLE_STRING -> serialize_asn1_printable_string_TLV

let parse_asn1_character_string_with_character_bound
  (t: character_string_type)
  (lb: asn1_value_int32_of_type t)
  (ub: asn1_value_int32_of_type t { lb <= ub })
: parser (parse_asn1_string_TLV_kind t) (asn1_string_with_character_bound_t t (count_character t) lb ub)
= match t with
  | IA5_STRING -> assert_norm (count_ia5_character == count_character IA5_STRING);
                  parse_asn1_ia5_string_TLV_with_character_bound lb ub
  | PRINTABLE_STRING
               -> assert_norm (count_printable_character == count_character PRINTABLE_STRING);
                  parse_asn1_printable_string_TLV_with_character_bound lb ub

let serialize_asn1_character_string_with_character_bound
  (t: character_string_type)
  (lb: asn1_value_int32_of_type t)
  (ub: asn1_value_int32_of_type t { lb <= ub })
: serializer (parse_asn1_character_string_with_character_bound t lb ub)
= match t with
  | IA5_STRING -> assert_norm (count_ia5_character == count_character IA5_STRING);
                  serialize_asn1_ia5_string_TLV_with_character_bound lb ub
  | PRINTABLE_STRING
               -> assert_norm (count_printable_character == count_character PRINTABLE_STRING);
                  serialize_asn1_printable_string_TLV_with_character_bound lb ub

let lemma_serialize_character_string_unfold
  (t: character_string_type)
  // (lb: asn1_value_int32_of_type t)
  // (ub: asn1_value_int32_of_type t { lb <= ub })
  // (x: asn1_string_with_character_bound_t t (count_character t) lb ub)
  (x: datatype_of_asn1_type t)
: Lemma (
    match t with
    | IA5_STRING -> predicate_serialize_asn1_string_TLV_unfold
                     (IA5_STRING)
                     (dfst)
                     (filter_asn1_ia5_string)
                     (synth_asn1_ia5_string)
                     (synth_asn1_ia5_string_inverse)
                     ()
                     (x)
    | PRINTABLE_STRING
                 -> predicate_serialize_asn1_string_TLV_unfold
                     (PRINTABLE_STRING)
                     (dfst)
                     (filter_asn1_printable_string)
                     (synth_asn1_printable_string)
                     (synth_asn1_printable_string_inverse)
                     ()
                     (x))
= match t with
  | IA5_STRING ->
                  // assert_norm ( t == IA5_STRING /\
                  //               len_of_character_string IA5_STRING == (fun (x:datatype_of_asn1_type IA5_STRING) -> dfst x) /\
                  //               count_character IA5_STRING == count_ia5_character /\
                  //               synth_character_string IA5_STRING == synth_asn1_ia5_string /\
                  //               synth_character_string_inverse IA5_STRING == synth_asn1_ia5_string_inverse );
                  // assert ( len_of_character_string IA5_STRING == len_of_character_string t /\
                  //          count_character IA5_STRING == count_character t /\
                  //          synth_character_string IA5_STRING == synth_character_string t /\
                  //          synth_character_string_inverse IA5_STRING == synth_character_string_inverse t /\
                  //          string_prf t == () );
                  lemma_serialize_asn1_ia5_string_TLV_unfold x
  | PRINTABLE_STRING
               -> lemma_serialize_asn1_printable_string_TLV_unfold x

let lemma_serialize_character_string_size
  (t: character_string_type)
  // (lb: asn1_value_int32_of_type t)
  // (ub: asn1_value_int32_of_type t { lb <= ub })
  // (x: asn1_string_with_character_bound_t t (count_character t) lb ub)
  (x: datatype_of_asn1_type t)
: Lemma (
    match t with
    | IA5_STRING -> predicate_serialize_asn1_string_TLV_size
                     (IA5_STRING)
                     (dfst)
                     (filter_asn1_ia5_string)
                     (synth_asn1_ia5_string)
                     (synth_asn1_ia5_string_inverse)
                     ()
                     (x)
    | PRINTABLE_STRING
                 -> predicate_serialize_asn1_string_TLV_size
                     (PRINTABLE_STRING)
                     (dfst)
                     (filter_asn1_printable_string)
                     (synth_asn1_printable_string)
                     (synth_asn1_printable_string_inverse)
                     ()
                     (x))
= match t with
  | IA5_STRING ->
                  // assert_norm ( t == IA5_STRING /\
                  //               len_of_character_string IA5_STRING == (fun (x:datatype_of_asn1_type IA5_STRING) -> dfst x) /\
                  //               count_character IA5_STRING == count_ia5_character /\
                  //               synth_character_string IA5_STRING == synth_asn1_ia5_string /\
                  //               synth_character_string_inverse IA5_STRING == synth_asn1_ia5_string_inverse );
                  // assert ( len_of_character_string IA5_STRING == len_of_character_string t /\
                  //          count_character IA5_STRING == count_character t /\
                  //          synth_character_string IA5_STRING == synth_character_string t /\
                  //          synth_character_string_inverse IA5_STRING == synth_character_string_inverse t /\
                  //          string_prf t == () );
                  lemma_serialize_asn1_ia5_string_TLV_size x
  | PRINTABLE_STRING
               -> lemma_serialize_asn1_printable_string_TLV_size x
