module ASN1.Spec.Value.IA5_STRING

open ASN1.Spec.Base
open LowParse.Spec.Bytes

open ASN1.Base
open ASN1.Spec.Tag
open ASN1.Spec.Length
open ASN1.Spec.Value.StringCombinator

open FStar.Integers

module B32 = FStar.Bytes

let synth_asn1_ia5_string_inverse len value
= value.c_str

let lemma_serialize_asn1_ia5_string_TLV_unfold x
= lemma_serialize_asn1_string_TLV_unfold
    (IA5_STRING)
    (fun c -> c.c_str_len)
    (filter_asn1_ia5_string)
    (synth_asn1_ia5_string)
    (synth_asn1_ia5_string_inverse)
    ()
    (x)

let lemma_serialize_asn1_ia5_string_TLV_size x
= lemma_serialize_asn1_string_TLV_size
    (IA5_STRING)
    (fun c -> c.c_str_len)
    (filter_asn1_ia5_string)
    (synth_asn1_ia5_string)
    (synth_asn1_ia5_string_inverse)
    ()
    (x)
