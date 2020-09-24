module ASN1.Spec.Value.IA5_STRING

open ASN1.Spec.Base
open LowParse.Spec.Bytes

open ASN1.Base
open ASN1.Spec.Tag
open ASN1.Spec.Length
open ASN1.Spec.Value.StringCombinator

open FStar.Integers

module B32 = FStar.Bytes

let synth_asn1_ia5_string
  (len: asn1_value_int32_of_type IA5_STRING)
  (s32: parse_filter_refine (filter_asn1_ia5_string len))
: GTot (value: datatype_of_asn1_type IA5_STRING{(dfst value) == len})
= (|len, s32|)

let lemma_synth_asn1_ia5_string_injective ()
= ()

noextract inline_for_extraction
let synth_asn1_ia5_string_inverse
  (len: asn1_value_int32_of_type IA5_STRING)
  (value: datatype_of_asn1_type IA5_STRING{(dfst value) == len})
: (s32: parse_filter_refine (filter_asn1_ia5_string len)
             { value == synth_asn1_ia5_string len s32 })
= dsnd value

// let parse_asn1_ia5_string
// = parse_asn1_string
//     (IA5_STRING)
//     (dfst)
//     (filter_asn1_ia5_string)
//     (synth_asn1_ia5_string)
//     (lemma_synth_asn1_ia5_string_injective ())

// let serialize_asn1_ia5_string
// = serialize_asn1_string
//     (IA5_STRING)
//     (dfst)
//     (filter_asn1_ia5_string)
//     (synth_asn1_ia5_string)
//     (synth_asn1_ia5_string_inverse)
//     (lemma_synth_asn1_ia5_string_injective ())

let lemma_serialize_asn1_ia5_string_unfold
= lemma_serialize_asn1_string_unfold
    (IA5_STRING)
    (dfst)
    (filter_asn1_ia5_string)
    (synth_asn1_ia5_string)
    (synth_asn1_ia5_string_inverse)
    (lemma_synth_asn1_ia5_string_injective ())

let lemma_serialize_asn1_ia5_string_size
= lemma_serialize_asn1_string_size
    (IA5_STRING)
    (dfst)
    (filter_asn1_ia5_string)
    (synth_asn1_ia5_string)
    (synth_asn1_ia5_string_inverse)
    (lemma_synth_asn1_ia5_string_injective ())


// let parse_asn1_ia5_string_TLV
// = parse_asn1_string_TLV
//     (IA5_STRING)
//     (dfst)
//     (filter_asn1_ia5_string)
//     (synth_asn1_ia5_string)
//     (lemma_synth_asn1_ia5_string_injective ())

// let serialize_asn1_ia5_string_TLV
// = serialize_asn1_string_TLV
//     (IA5_STRING)
//     (dfst)
//     (filter_asn1_ia5_string)
//     (synth_asn1_ia5_string)
//     (synth_asn1_ia5_string_inverse)
//     (lemma_synth_asn1_ia5_string_injective ())

let lemma_serialize_asn1_ia5_string_TLV_unfold x
= lemma_serialize_asn1_string_TLV_unfold
    (IA5_STRING)
    (dfst)
    (filter_asn1_ia5_string)
    (synth_asn1_ia5_string)
    (synth_asn1_ia5_string_inverse)
    (lemma_synth_asn1_ia5_string_injective ())
    (x)

let lemma_serialize_asn1_ia5_string_TLV_size x
= lemma_serialize_asn1_string_TLV_size
    (IA5_STRING)
    (dfst)
    (filter_asn1_ia5_string)
    (synth_asn1_ia5_string)
    (synth_asn1_ia5_string_inverse)
    (lemma_synth_asn1_ia5_string_injective ())
    (x)

let count_ia5_character x
= dfst x

let parse_asn1_ia5_string_TLV_with_character_bound lb ub
= parse_asn1_string_TLV_with_character_bound
    (IA5_STRING)
    (dfst)
    (filter_asn1_ia5_string)
    (synth_asn1_ia5_string)
    (lemma_synth_asn1_ia5_string_injective ())
    (count_ia5_character)
    (lb)
    (ub)

let serialize_asn1_ia5_string_TLV_with_character_bound lb ub
= serialize_asn1_string_TLV_with_character_bound
    (IA5_STRING)
    (dfst)
    (filter_asn1_ia5_string)
    (synth_asn1_ia5_string)
    (synth_asn1_ia5_string_inverse)
    (lemma_synth_asn1_ia5_string_injective ())
    (count_ia5_character)
    (lb)
    (ub)
