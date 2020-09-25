module ASN1.Spec.Value.PRINTABLE_STRING

open ASN1.Spec.Base

open ASN1.Base
open ASN1.Spec.Value.StringCombinator

open FStar.Integers

module B32 = FStar.Bytes

let filter_asn1_printable_string
  (len: asn1_value_int32_of_type PRINTABLE_STRING)
  (s32: B32.lbytes32 len)
: GTot (bool)
= let s = B32.reveal s32 in
  Seq.for_all valid_PRINTABLE_byte s

let synth_asn1_printable_string
  (len: asn1_value_int32_of_type PRINTABLE_STRING)
  (s32: parse_filter_refine (filter_asn1_printable_string len))
: GTot (value: datatype_of_asn1_type PRINTABLE_STRING{(dfst value) == len})
= (|len, s32|)

noextract inline_for_extraction
val synth_asn1_printable_string_inverse
  (len: asn1_value_int32_of_type PRINTABLE_STRING)
  (value: datatype_of_asn1_type PRINTABLE_STRING{(dfst value) == len})
: Tot (s32: parse_filter_refine (filter_asn1_printable_string len)
             { value == synth_asn1_printable_string len s32 })

let parse_asn1_printable_string
= parse_asn1_string
    (PRINTABLE_STRING)
    (dfst)
    (filter_asn1_printable_string)
    (synth_asn1_printable_string)
    ()

let serialize_asn1_printable_string
= serialize_asn1_string
    (PRINTABLE_STRING)
    (dfst)
    (filter_asn1_printable_string)
    (synth_asn1_printable_string)
    (synth_asn1_printable_string_inverse)
    ()

let lemma_serialize_asn1_printable_string_unfold
= lemma_serialize_asn1_string_unfold
    (PRINTABLE_STRING)
    (dfst)
    (filter_asn1_printable_string)
    (synth_asn1_printable_string)
    (synth_asn1_printable_string_inverse)
    ()

let lemma_serialize_asn1_printable_string_size
= lemma_serialize_asn1_string_size
    (PRINTABLE_STRING)
    (dfst)
    (filter_asn1_printable_string)
    (synth_asn1_printable_string)
    (synth_asn1_printable_string_inverse)
    ()

let parse_asn1_printable_string_TLV_kind = parse_asn1_string_TLV_kind PRINTABLE_STRING

let parse_asn1_printable_string_TLV
= parse_asn1_string_TLV
    (PRINTABLE_STRING)
    (dfst)
    (filter_asn1_printable_string)
    (synth_asn1_printable_string)
    ()

let serialize_asn1_printable_string_TLV
= serialize_asn1_string_TLV
    (PRINTABLE_STRING)
    (dfst)
    (filter_asn1_printable_string)
    (synth_asn1_printable_string)
    (synth_asn1_printable_string_inverse)
    ()

let lemma_serialize_asn1_printable_string_TLV_unfold
  (x: datatype_of_asn1_type PRINTABLE_STRING)
: Lemma (
  predicate_serialize_asn1_string_TLV_unfold
    (PRINTABLE_STRING)
    (dfst)
    (filter_asn1_printable_string)
    (synth_asn1_printable_string)
    (synth_asn1_printable_string_inverse)
    ()
    (x)
)
= lemma_serialize_asn1_string_TLV_unfold
    (PRINTABLE_STRING)
    (dfst)
    (filter_asn1_printable_string)
    (synth_asn1_printable_string)
    (synth_asn1_printable_string_inverse)
    ()
    (x)

let lemma_serialize_asn1_printable_string_TLV_size
  (x: datatype_of_asn1_type PRINTABLE_STRING)
: Lemma (
  predicate_serialize_asn1_string_TLV_size
    (PRINTABLE_STRING)
    (dfst)
    (filter_asn1_printable_string)
    (synth_asn1_printable_string)
    (synth_asn1_printable_string_inverse)
    ()
    (x)
)
= lemma_serialize_asn1_string_TLV_size
    (PRINTABLE_STRING)
    (dfst)
    (filter_asn1_printable_string)
    (synth_asn1_printable_string)
    (synth_asn1_printable_string_inverse)
    ()
    (x)

let count_printable_character
  (x: datatype_of_asn1_type PRINTABLE_STRING)
: Tot (asn1_int32)
= dfst x

let parse_asn1_printable_string_TLV_with_character_bound
  (lb: asn1_value_int32_of_type PRINTABLE_STRING)
  (ub: asn1_value_int32_of_type PRINTABLE_STRING { lb <= ub })
: parser parse_asn1_printable_string_TLV_kind (asn1_string_with_character_bound_t PRINTABLE_STRING count_printable_character lb ub)
= parse_asn1_string_TLV_with_character_bound
    (PRINTABLE_STRING)
    (dfst)
    (filter_asn1_printable_string)
    (synth_asn1_printable_string)
    ()
    (count_printable_character)
    (lb)
    (ub)

let serialize_asn1_printable_string_TLV_with_character_bound
  (lb: asn1_value_int32_of_type PRINTABLE_STRING)
  (ub: asn1_value_int32_of_type PRINTABLE_STRING { lb <= ub })
: serializer (parse_asn1_printable_string_TLV_with_character_bound lb ub)
= serialize_asn1_string_TLV_with_character_bound
    (PRINTABLE_STRING)
    (dfst)
    (filter_asn1_printable_string)
    (synth_asn1_printable_string)
    (synth_asn1_printable_string_inverse)
    ()
    (count_printable_character)
    (lb)
    (ub)
