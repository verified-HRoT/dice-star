module ASN1.Spec.Value.OCTET_STRING

open ASN1.Spec.Base
open LowParse.Spec.Bytes

open ASN1.Base
open ASN1.Spec.Tag
open ASN1.Spec.Length

open FStar.Integers

module B32 = FStar.Bytes

(* NOTE: Read after `ASN1.Spec.Tag`, `ASN1.Spec.Length`, `ASN1.Spec.Value.OCTET_STRING` *)

(* NOTE: This module defines:
         1) The ASN1 `OCTET_STRING` Value Parser and Serializer
         2) The ASN1 `OCTET_STRING` TLV Parser and Serializer

         And each part is organized as:
         1) Aux (ghost) functions with prefix `filter_` to filter out invalid input bytes
         2) Aux (ghost) functions with prefix `synth_` to decode the valid input bytes into our
            representation of OCTET_STRING values. These functions are injective.
         3) Aux (ghost) functions with prefix `synth_` and suffix `_inverse` to encode our
            representation of OCTET_STRING into bytes. These functions are the inverse of
            corresponding synth functions.
         4) Functions with the prefix `parse_` are parsers constructed using parser combinators and
            aux functions.
         5) Functions with the prefix `serialize_` are serializers constructed using serializer
            combinators and aux functions.
         6) Lemma with suffix `_unfold` reveals the computation of parser/serialzier.
         7) Lemma with suffix `_size` reveals the length of a serialization.
*)

///////////////////////////////////////////////////////////
//// ASN1 `OCTET_STRING` Value Parser and Serializer
//////////////////////////////////////////////////////////

/// Decodes input bytes into our representation of a OCTET_STRING value
let synth_asn1_octet_string l s32
= (|u l, s32|)


/// Encodes our representation of a OCTET_STRING into bytes
let synth_asn1_octet_string_inverse l value
= dsnd value

///
/// Parser
///
let parse_asn1_octet_string l
= parse_flbytes l
  `parse_synth`
  synth_asn1_octet_string l

///
/// Serializer
///
let serialize_asn1_octet_string l
= serialize_synth
  (* p1 *) (parse_flbytes l)
  (* f2 *) (synth_asn1_octet_string l)
  (* s1 *) (serialize_flbytes l)
  (* g1 *) (synth_asn1_octet_string_inverse l)
  (* Prf*) ()


///
/// Lemmas
///

/// Reveal the computation of parse
let lemma_parse_asn1_octet_string_unfold l input
= parse_synth_eq
  (* p1 *) (parse_flbytes l)
  (* f2 *) (synth_asn1_octet_string l)
  (* in *) (input)

/// Reveal the computation of serialize
let lemma_serialize_asn1_octet_string_unfold l value
= serialize_synth_eq
  (* p1 *) (parse_flbytes l)
  (* f2 *) (synth_asn1_octet_string l)
  (* s1 *) (serialize_flbytes l)
  (* g1 *) (synth_asn1_octet_string_inverse l)
  (* Prf*) ()
  (* in *) (value)

/// Reveal the length of a serialzation
let lemma_serialize_asn1_octet_string_size l value
= parser_kind_prop_equiv (parse_asn1_octet_string_kind l) (parse_asn1_octet_string l);
  lemma_serialize_asn1_octet_string_unfold l value


///////////////////////////////////////////////////////////
//// ASN1 `OCTET_STRING` TLV Parser and Serializer
///////////////////////////////////////////////////////////

/// parser tag for the `tagged_union` combinators
let parser_tag_of_octet_string x
= (OCTET_STRING, dfst x)

///
/// A pair of aux parser/serializer, which explicitly coerce the `OCTET_STRING` value
/// between the subtype used by `OCTET_STRING` value parser/serialzier and `OCTET_STRING`
/// TLV parser/serializer.
///
/// NOTE: I found that have this aux parser explicitly defined will make the prove of
///       `_unfold` lemmas simpler.
///

/// Convert an `OCTET_STRING` value from the subtype used by its value parser to the subtype
/// used by its TLV parser/serializer
/// (value : subtype_{value}) <: subtype_{TLV}
let synth_asn1_octet_string_V tag value
= value

/// Convert an `OCTET_STRING` value from the subtype used by its TLV parser to the subtype
/// used by its value parser/serializer
/// (value : subtype_{TLV}) <: subtype_{value}
let synth_asn1_octet_string_V_inverse tag value'
= value'


///
/// Aux parser
///
let parse_asn1_octet_string_V tag
= weak_kind_of_type OCTET_STRING
  `weaken`
  parse_asn1_octet_string (v (snd tag))
  `parse_synth`
  synth_asn1_octet_string_V tag

///
/// Aux serializer
///
let serialize_asn1_octet_string_V tag
= serialize_synth
  (* p1 *) (weak_kind_of_type OCTET_STRING
            `weaken`
            parse_asn1_octet_string (v (snd tag)))
  (* f2 *) (synth_asn1_octet_string_V tag)
  (* s1 *) (weak_kind_of_type OCTET_STRING
            `serialize_weaken`
            serialize_asn1_octet_string (v (snd tag)))
  (* g1 *) (synth_asn1_octet_string_V_inverse tag)
  (* prf*) ()

///
/// Lemmas
///

/// Reveal the computation of parse
let lemma_parse_asn1_octet_string_V_unfold tag input
= parse_synth_eq
  (* p1 *) (weak_kind_of_type OCTET_STRING
            `weaken`
            parse_asn1_octet_string (v (snd tag)))
  (* f2 *) (synth_asn1_octet_string_V tag)
  (* in *) input

/// Reveal the computation of serialzation
noextract
let lemma_serialize_asn1_octet_string_V_unfold
  (tag: (the_asn1_tag OCTET_STRING & asn1_value_int32_of_type OCTET_STRING))
  (value: refine_with_tag parser_tag_of_octet_string tag)
: Lemma (
  serialize (serialize_asn1_octet_string_V tag) value ==
  serialize (serialize_asn1_octet_string (v (snd tag))) value
)
= serialize_synth_eq
  (* p1 *) (weak_kind_of_type OCTET_STRING
            `weaken`
            parse_asn1_octet_string (v (snd tag)))
  (* f2 *) (synth_asn1_octet_string_V tag)
  (* s1 *) (weak_kind_of_type OCTET_STRING
            `serialize_weaken`
            serialize_asn1_octet_string (v (snd tag)))
  (* g1 *) (synth_asn1_octet_string_V_inverse tag)
  (* prf*) ()
  (* in *) (value)


//////////////////////////////////////////////////////////
///
/// ASN1 `OCTET_STRING` TLV Parser
///
let parse_asn1_octet_string_TLV
= parse_tagged_union
  (* pt *) (parse_asn1_tag_of_type OCTET_STRING
            `nondep_then`
            parse_asn1_length_of_type OCTET_STRING)
  (* tg *) (parser_tag_of_octet_string)
  (* p  *) (parse_asn1_octet_string_V)

///
/// Serializer
///
let serialize_asn1_octet_string_TLV
= serialize_tagged_union
  (* st *) (serialize_asn1_tag_of_type OCTET_STRING
            `serialize_nondep_then`
            serialize_asn1_length_of_type OCTET_STRING)
  (* tg *) (parser_tag_of_octet_string)
  (* s  *) (serialize_asn1_octet_string_V)

///
/// Lemmas
///

/// Reveal the computation of parse
#restart-solver
#push-options "--z3rlimit 32 --initial_ifuel 8"
noextract
let lemma_parse_asn1_octet_string_TLV_unfold input
= nondep_then_eq
  (* p1 *) (parse_asn1_tag_of_type OCTET_STRING)
  (* p2 *) (parse_asn1_length_of_type OCTET_STRING)
  (* in *) (input);

  let parsed_tag
  = parse (parse_asn1_tag_of_type OCTET_STRING
           `nondep_then`
           parse_asn1_length_of_type OCTET_STRING) input in
  if (Some? parsed_tag) then
  ( let Some (tag, consumed) = parsed_tag in
    lemma_parse_asn1_octet_string_V_unfold tag (Seq.slice input consumed (Seq.length input)) );

  parse_tagged_union_eq
  (* pt *) (parse_asn1_tag_of_type OCTET_STRING
            `nondep_then`
            parse_asn1_length_of_type OCTET_STRING)
  (* tg *) (parser_tag_of_octet_string)
  (* p  *) (parse_asn1_octet_string_V)
  (* in *) (input)
#pop-options

/// Reveal the computation of serialize
#push-options "--z3rlimit 32"
let lemma_serialize_asn1_octet_string_TLV_unfold value
= serialize_nondep_then_eq
  (* s1 *) (serialize_asn1_tag_of_type OCTET_STRING)
  (* s2 *) (serialize_asn1_length_of_type OCTET_STRING)
  (* in *) (parser_tag_of_octet_string value);
  lemma_serialize_asn1_octet_string_V_unfold (parser_tag_of_octet_string value) value;
  serialize_tagged_union_eq
  (* st *) (serialize_asn1_tag_of_type OCTET_STRING
            `serialize_nondep_then`
            serialize_asn1_length_of_type OCTET_STRING)
  (* tg *) (parser_tag_of_octet_string)
  (* s  *) (serialize_asn1_octet_string_V)
  (* in *) (value)
#pop-options

/// Reveal the size of a serialzation
#push-options "--z3rlimit 16"
let lemma_serialize_asn1_octet_string_TLV_size value
= lemma_serialize_asn1_octet_string_TLV_unfold value;
  lemma_serialize_asn1_tag_of_type_size OCTET_STRING OCTET_STRING;
  lemma_serialize_asn1_length_size (dfst value);
  serialize_asn1_length_of_type_eq OCTET_STRING (dfst value);
  lemma_serialize_asn1_octet_string_size (v (dfst value)) value
#pop-options
