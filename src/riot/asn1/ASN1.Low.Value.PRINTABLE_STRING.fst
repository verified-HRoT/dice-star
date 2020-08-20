module ASN1.Low.Value.PRINTABLE_STRING

open ASN1.Base
open ASN1.Spec.Value.PRINTABLE_STRING
open ASN1.Low.Value.StringTypes
open ASN1.Low.Base
open LowParse.Low.Bytes

open ASN1.Spec.Tag
open ASN1.Spec.Length
open ASN1.Low.Tag
open ASN1.Low.Length

open FStar.Integers

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module MB = LowStar.Monotonic.Buffer
module B = LowStar.Buffer
module Cast = FStar.Int.Cast

module B32 = FStar.Bytes

let serialize32_asn1_printable_string_TLV_backwards
: serializer32_backwards (serialize_asn1_printable_string_TLV)
= serialize32_asn1_string_TLV_backwards
    (PRINTABLE_STRING)
    (dfst)
    (filter_asn1_printable_string)
    (synth_asn1_printable_string)
    (synth_asn1_printable_string_inverse)
    ()

let serialize32_asn1_printable_string_TLV_with_character_bound_backwards
// : serializer32_backwards (serialize_asn1_printable_string_TLV_with_character_bound lb ub)
= serialize32_asn1_string_TLV_with_character_bound_backwards
    (PRINTABLE_STRING)
    (dfst)
    (filter_asn1_printable_string)
    (synth_asn1_printable_string)
    (synth_asn1_printable_string_inverse)
    ()
    (count_printable_character)
