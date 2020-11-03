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
= value.c_str
