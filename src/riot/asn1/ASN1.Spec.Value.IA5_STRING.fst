module ASN1.Spec.Value.IA5_STRING

open ASN1.Spec.Base
open LowParse.Spec.Bytes

open ASN1.Base
open ASN1.Spec.Tag
open ASN1.Spec.Length
open ASN1.Spec.Value.StringCombinator

open FStar.Integers

module B32 = FStar.Bytes

let lemma_synth_asn1_ia5_string_injective () = ()

let synth_asn1_ia5_string_inverse len value
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

let parse_asn1_ia5_string_TLV
= parse_asn1_string_TLV
    (IA5_STRING)
    (dfst)
    (filter_asn1_ia5_string)
    (synth_asn1_ia5_string)
    ()

let serialize_asn1_ia5_string_TLV
= serialize_asn1_string_TLV
    (IA5_STRING)
    (dfst)
    (filter_asn1_ia5_string)
    (synth_asn1_ia5_string)
    (synth_asn1_ia5_string_inverse)
    ()

let lemma_serialize_asn1_ia5_string_TLV_unfold x
= lemma_serialize_asn1_string_TLV_unfold
    (IA5_STRING)
    (dfst)
    (filter_asn1_ia5_string)
    (synth_asn1_ia5_string)
    (synth_asn1_ia5_string_inverse)
    ()
    (x)

let lemma_serialize_asn1_ia5_string_TLV_size x
= lemma_serialize_asn1_string_TLV_size
    (IA5_STRING)
    (dfst)
    (filter_asn1_ia5_string)
    (synth_asn1_ia5_string)
    (synth_asn1_ia5_string_inverse)
    ()
    (x)

let parse_asn1_ia5_string_TLV_with_character_bound lb ub
= parse_asn1_string_TLV_with_character_bound
    (IA5_STRING)
    (dfst)
    (filter_asn1_ia5_string)
    (synth_asn1_ia5_string)
    ()
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
    ()
    (count_ia5_character)
    (lb)
    (ub)
