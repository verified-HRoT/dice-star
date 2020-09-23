module ASN1.Spec.Value.IA5_STRING

open ASN1.Spec.Base
open LowParse.Spec.Bytes

open ASN1.Base
open ASN1.Spec.Tag
open ASN1.Spec.Length
open ASN1.Spec.Value.StringCombinator

open FStar.Integers

module B32 = FStar.Bytes

let filter_asn1_ia5_string
  (len: asn1_value_int32_of_type IA5_STRING)
  (s32: B32.lbytes32 len)
: GTot (bool)
= let s = B32.reveal s32 in
  Seq.for_all valid_IA5_byte s

let synth_asn1_ia5_string
  (len: asn1_value_int32_of_type IA5_STRING)
  (s32: parse_filter_refine (filter_asn1_ia5_string len))
: GTot (value: datatype_of_asn1_type IA5_STRING{(dfst value) == len})
= (|len, s32|)

noextract inline_for_extraction
let synth_asn1_ia5_string_inverse
  (len: asn1_value_int32_of_type IA5_STRING)
  (value: datatype_of_asn1_type IA5_STRING{(dfst value) == len})
: Tot (s32: parse_filter_refine (filter_asn1_ia5_string len)
             { value == synth_asn1_ia5_string len s32 })
= dsnd value

let parse_asn1_ia5_string
= parse_asn1_string
    (IA5_STRING)
    (dfst)
    (filter_asn1_ia5_string)
    (synth_asn1_ia5_string)
    ()

let serialize_asn1_ia5_string
= serialize_asn1_string
    (IA5_STRING)
    (dfst)
    (filter_asn1_ia5_string)
    (synth_asn1_ia5_string)
    (synth_asn1_ia5_string_inverse)
    ()

let lemma_serialize_asn1_ia5_string_unfold
= lemma_serialize_asn1_string_unfold
    (IA5_STRING)
    (dfst)
    (filter_asn1_ia5_string)
    (synth_asn1_ia5_string)
    (synth_asn1_ia5_string_inverse)
    ()

let lemma_serialize_asn1_ia5_string_size
= lemma_serialize_asn1_string_size
    (IA5_STRING)
    (dfst)
    (filter_asn1_ia5_string)
    (synth_asn1_ia5_string)
    (synth_asn1_ia5_string_inverse)
    ()

let parse_asn1_ia5_string_TLV_kind = parse_asn1_string_TLV_kind IA5_STRING
let parse_asn1_ia5_string_TLV
: parser parse_asn1_ia5_string_TLV_kind (datatype_of_asn1_type IA5_STRING)
= parse_asn1_string_TLV
    (IA5_STRING)
    (dfst)
    (filter_asn1_ia5_string)
    (synth_asn1_ia5_string)
    ()

let serialize_asn1_ia5_string_TLV
: serializer (parse_asn1_ia5_string_TLV)
= serialize_asn1_string_TLV
    (IA5_STRING)
    (dfst)
    (filter_asn1_ia5_string)
    (synth_asn1_ia5_string)
    (synth_asn1_ia5_string_inverse)
    ()

let lemma_serialize_asn1_ia5_string_TLV_unfold
  (x: datatype_of_asn1_type IA5_STRING)
: Lemma (
  predicate_serialize_asn1_string_TLV_unfold
    (IA5_STRING)
    (dfst)
    (filter_asn1_ia5_string)
    (synth_asn1_ia5_string)
    (synth_asn1_ia5_string_inverse)
    ()
    (x)
)
= lemma_serialize_asn1_string_TLV_unfold
    (IA5_STRING)
    (dfst)
    (filter_asn1_ia5_string)
    (synth_asn1_ia5_string)
    (synth_asn1_ia5_string_inverse)
    ()
    (x)

let lemma_serialize_asn1_ia5_string_TLV_size
  (x: datatype_of_asn1_type IA5_STRING)
: Lemma (
  predicate_serialize_asn1_string_TLV_size
    (IA5_STRING)
    (dfst)
    (filter_asn1_ia5_string)
    (synth_asn1_ia5_string)
    (synth_asn1_ia5_string_inverse)
    ()
    (x)
)
= lemma_serialize_asn1_string_TLV_size
    (IA5_STRING)
    (dfst)
    (filter_asn1_ia5_string)
    (synth_asn1_ia5_string)
    (synth_asn1_ia5_string_inverse)
    ()
    (x)

let count_ia5_character
  (x: datatype_of_asn1_type IA5_STRING)
: Tot (asn1_int32)
= dfst x

let parse_asn1_ia5_string_TLV_with_character_bound
  (lb: asn1_value_int32_of_type IA5_STRING)
  (ub: asn1_value_int32_of_type IA5_STRING { lb <= ub })
: parser parse_asn1_ia5_string_TLV_kind (asn1_string_with_character_bound_t IA5_STRING count_ia5_character lb ub)
= parse_asn1_string_TLV_with_character_bound
    (IA5_STRING)
    (dfst)
    (filter_asn1_ia5_string)
    (synth_asn1_ia5_string)
    ()
    (count_ia5_character)
    (lb)
    (ub)

let serialize_asn1_ia5_string_TLV_with_character_bound
  (lb: asn1_value_int32_of_type IA5_STRING)
  (ub: asn1_value_int32_of_type IA5_STRING { lb <= ub })
: serializer (parse_asn1_ia5_string_TLV_with_character_bound lb ub)
= serialize_asn1_string_TLV_with_character_bound
    (IA5_STRING)
    (dfst)
    (filter_asn1_ia5_string)
    (synth_asn1_ia5_string)
    (synth_asn1_ia5_string_inverse)
    ()
    (count_ia5_character)
    (lb)
    (ub)
