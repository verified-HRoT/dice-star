module ASN1.Spec.Value.PRINTABLE_STRING

open ASN1.Spec.Base

open ASN1.Base
open ASN1.Spec.Value.StringCombinator

open FStar.Integers

module B32 = FStar.Bytes

(* ZT: Maybe we don't need to hide this module, which is
       just instantiating another mudule. Since the lemmas'
       types are also instantiating some meta predicates,
       they are meanlingless unless a module friends this
       module. *)

let filter_asn1_printable_string
  (len: asn1_value_int32_of_type PRINTABLE_STRING)
  (s32: B32.lbytes32 len)
: GTot (bool)
= let s = B32.reveal s32 in
  Seq.for_all valid_PRINTABLE_byte s

val synth_asn1_printable_string
  (len: asn1_value_int32_of_type PRINTABLE_STRING)
  (s32: parse_filter_refine (filter_asn1_printable_string len))
: GTot (value: datatype_of_asn1_type PRINTABLE_STRING{(dfst value) == len})

val lemma_synth_asn1_printable_string_injective (_: unit)
: Lemma (
  forall (len: asn1_value_int32_of_type (PRINTABLE_STRING)).
    synth_injective (synth_asn1_printable_string len)
)

noextract inline_for_extraction
val synth_asn1_printable_string_inverse
  (len: asn1_value_int32_of_type PRINTABLE_STRING)
  (value: datatype_of_asn1_type PRINTABLE_STRING{(dfst value) == len})
: (s32: parse_filter_refine (filter_asn1_printable_string len)
             { value == synth_asn1_printable_string len s32 })

(* ZT: Exposing those two since the type of lemmas below
       depends on their implementation *)
let parse_asn1_printable_string
  (len: asn1_value_int32_of_type PRINTABLE_STRING)
: parser (parse_asn1_string_kind PRINTABLE_STRING len)
         (x: datatype_of_asn1_type PRINTABLE_STRING {dfst x == len})
= parse_asn1_string
    (PRINTABLE_STRING)
    (dfst)
    (filter_asn1_printable_string)
    (synth_asn1_printable_string)
    (lemma_synth_asn1_printable_string_injective ())
    (len)

let serialize_asn1_printable_string
  (len: asn1_value_int32_of_type PRINTABLE_STRING)
: serializer (parse_asn1_printable_string len)
= serialize_asn1_string
    (PRINTABLE_STRING)
    (dfst)
    (filter_asn1_printable_string)
    (synth_asn1_printable_string)
    (synth_asn1_printable_string_inverse)
    (lemma_synth_asn1_printable_string_injective ())
    (len)

val lemma_serialize_asn1_printable_string_unfold
  (len: asn1_value_int32_of_type PRINTABLE_STRING)
  (x: datatype_of_asn1_type PRINTABLE_STRING { dfst x == len })
: Lemma (
  predicate_serialize_asn1_string_unfold
    (PRINTABLE_STRING)
    (dfst)
    (filter_asn1_printable_string)
    (synth_asn1_printable_string)
    (synth_asn1_printable_string_inverse)
    (lemma_synth_asn1_printable_string_injective ())
    (len)
    (x)
)

val lemma_serialize_asn1_printable_string_size
  (len: asn1_value_int32_of_type PRINTABLE_STRING)
  (x: datatype_of_asn1_type PRINTABLE_STRING { dfst x == len })
: Lemma (
  predicate_serialize_asn1_string_size
    (PRINTABLE_STRING)
    (dfst)
    (filter_asn1_printable_string)
    (synth_asn1_printable_string)
    (synth_asn1_printable_string_inverse)
    (lemma_synth_asn1_printable_string_injective ())
    (len)
    (x)
)

let parse_asn1_printable_string_TLV_kind = parse_asn1_string_TLV_kind PRINTABLE_STRING

let parse_asn1_printable_string_TLV
: parser parse_asn1_printable_string_TLV_kind (datatype_of_asn1_type PRINTABLE_STRING)
= parse_asn1_string_TLV
    (PRINTABLE_STRING)
    (dfst)
    (filter_asn1_printable_string)
    (synth_asn1_printable_string)
    (lemma_synth_asn1_printable_string_injective ())

let serialize_asn1_printable_string_TLV
: serializer (parse_asn1_printable_string_TLV)
= serialize_asn1_string_TLV
    (PRINTABLE_STRING)
    (dfst)
    (filter_asn1_printable_string)
    (synth_asn1_printable_string)
    (synth_asn1_printable_string_inverse)
    (lemma_synth_asn1_printable_string_injective ())

val lemma_serialize_asn1_printable_string_TLV_unfold
  (x: datatype_of_asn1_type PRINTABLE_STRING)
: Lemma (
  predicate_serialize_asn1_string_TLV_unfold
    (PRINTABLE_STRING)
    (dfst)
    (filter_asn1_printable_string)
    (synth_asn1_printable_string)
    (synth_asn1_printable_string_inverse)
    (lemma_synth_asn1_printable_string_injective ())
    (x)
)

val lemma_serialize_asn1_printable_string_TLV_size
  (x: datatype_of_asn1_type PRINTABLE_STRING)
: Lemma (
  predicate_serialize_asn1_string_TLV_size
    (PRINTABLE_STRING)
    (dfst)
    (filter_asn1_printable_string)
    (synth_asn1_printable_string)
    (synth_asn1_printable_string_inverse)
    (lemma_synth_asn1_printable_string_injective ())
    (x)
)

(* ZT: Consider to expose this if anything in `X509.BasicFields.RelativeDistinguishedName` got blocked. *)
val count_printable_character
  (x: datatype_of_asn1_type PRINTABLE_STRING)
: (asn1_int32)

val parse_asn1_printable_string_TLV_with_character_bound
  (lb: asn1_value_int32_of_type PRINTABLE_STRING)
  (ub: asn1_value_int32_of_type PRINTABLE_STRING { lb <= ub })
: parser parse_asn1_printable_string_TLV_kind (asn1_string_with_character_bound_t PRINTABLE_STRING count_printable_character lb ub)

val serialize_asn1_printable_string_TLV_with_character_bound
  (lb: asn1_value_int32_of_type PRINTABLE_STRING)
  (ub: asn1_value_int32_of_type PRINTABLE_STRING { lb <= ub })
: serializer (parse_asn1_printable_string_TLV_with_character_bound lb ub)

