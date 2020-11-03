module ASN1.Low.Value.PRINTABLE_STRING

open ASN1.Base
open ASN1.Spec.Value.PRINTABLE_STRING
open ASN1.Low.Value.StringCombinator
open ASN1.Low.Base

open ASN1.Low.Tag
open ASN1.Low.Length

open FStar.Integers

friend ASN1.Spec.Value.PRINTABLE_STRING

let serialize32_asn1_printable_string_TLV_backwards
= serialize32_asn1_string_TLV_backwards
    (PRINTABLE_STRING)
    (dfst)
    (filter_asn1_printable_string)
    (synth_asn1_printable_string)
    (synth_asn1_printable_string_inverse)
    ()

let serialize32_asn1_printable_string_TLV_with_character_bound_backwards lb ub
= serialize32_asn1_string_TLV_with_character_bound_backwards
    (PRINTABLE_STRING)
    (dfst)
    (filter_asn1_printable_string)
    (synth_asn1_printable_string)
    (synth_asn1_printable_string_inverse)
    ()
    (count_printable_character)
    (lb)
    (ub)
