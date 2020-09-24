module ASN1.Spec.Value.PRINTABLE_STRING

open ASN1.Spec.Base
open LowParse.Spec.Bytes

open ASN1.Base
open ASN1.Spec.Tag
open ASN1.Spec.Length
open ASN1.Spec.Value.StringCombinator

open FStar.Integers

module B32 = FStar.Bytes

let synth_asn1_printable_string_inverse len value
= dsnd value

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

let parse_asn1_printable_string_TLV_with_character_bound lb ub
= parse_asn1_string_TLV_with_character_bound
    (PRINTABLE_STRING)
    (dfst)
    (filter_asn1_printable_string)
    (synth_asn1_printable_string)
    ()
    (count_printable_character)
    (lb)
    (ub)

let serialize_asn1_printable_string_TLV_with_character_bound lb ub
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
