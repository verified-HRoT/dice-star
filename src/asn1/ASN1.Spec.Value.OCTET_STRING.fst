module ASN1.Spec.Value.OCTET_STRING

open LowParse.Spec.Base
open LowParse.Spec.Combinators
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
noextract
let synth_asn1_octet_string
  (l: asn1_value_length_of_type OCTET_STRING)
  (s32: B32.lbytes l)
: GTot (value: datatype_of_asn1_type OCTET_STRING{v (dfst value) == l})
= (|u l, s32|)


/// Encodes our representation of a OCTET_STRING into bytes
noextract
let synth_asn1_octet_string_inverse
  (l: asn1_value_length_of_type OCTET_STRING)
  (value: datatype_of_asn1_type OCTET_STRING{v (dfst value) == l})
: GTot (s32: B32.lbytes l{ value == synth_asn1_octet_string l s32 })
= dsnd value

inline_for_extraction
let parse_asn1_octet_string_kind (l: asn1_value_length_of_type OCTET_STRING) = total_constant_size_parser_kind l

///
/// Parser
///
noextract
let parse_asn1_octet_string
  (l: asn1_value_length_of_type OCTET_STRING)
: parser (parse_asn1_octet_string_kind l) (x: datatype_of_asn1_type OCTET_STRING{v (dfst x) == l})
= parse_flbytes l
  `parse_synth`
  synth_asn1_octet_string l

///
/// Serializer
///
noextract
let serialize_asn1_octet_string
  (l: asn1_value_length_of_type OCTET_STRING)
: serializer (parse_asn1_octet_string l)
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
noextract
let parse_asn1_octet_string_unfold
  (l: asn1_value_length_of_type OCTET_STRING)
  (input: bytes)
: Lemma (
  parse (parse_asn1_octet_string l) input ==
 (match parse (parse_flbytes l) input with
  | None -> None
  | Some (ls, consumed) -> Some (synth_asn1_octet_string l ls, consumed)))
= parse_synth_eq
  (* p1 *) (parse_flbytes l)
  (* f2 *) (synth_asn1_octet_string l)
  (* in *) (input)

/// Reveal the computation of serialize
noextract
let serialize_asn1_octet_string_unfold
  (l: asn1_value_length_of_type OCTET_STRING)
  (value: datatype_of_asn1_type OCTET_STRING{v (dfst value) == l})
: Lemma (
  serialize (serialize_asn1_octet_string l) value ==
  serialize (serialize_flbytes l) (synth_asn1_octet_string_inverse l value))
= serialize_synth_eq
  (* p1 *) (parse_flbytes l)
  (* f2 *) (synth_asn1_octet_string l)
  (* s1 *) (serialize_flbytes l)
  (* g1 *) (synth_asn1_octet_string_inverse l)
  (* Prf*) ()
  (* in *) (value)

/// Reveal the length of a serialzation
noextract
let serialize_asn1_octet_string_size
  (l: asn1_value_length_of_type OCTET_STRING)
  (value: datatype_of_asn1_type OCTET_STRING{v (dfst value) == l})
: Lemma (
  Seq.length (serialize (serialize_asn1_octet_string l) value) == l)
= parser_kind_prop_equiv (parse_asn1_octet_string_kind l) (parse_asn1_octet_string l);
  serialize_asn1_octet_string_unfold l value


///////////////////////////////////////////////////////////
//// ASN1 `OCTET_STRING` TLV Parser and Serializer
///////////////////////////////////////////////////////////

/// parser tag for the `tagged_union` combinators
noextract
let parser_tag_of_octet_string
  (x: datatype_of_asn1_type OCTET_STRING)
: GTot (the_asn1_type OCTET_STRING & asn1_value_int32_of_type OCTET_STRING)
= (OCTET_STRING, dfst x)

noextract
let parse_asn1_octet_string_TLV_kind
: parser_kind
= parse_asn1_tag_kind
  `and_then_kind`
  parse_asn1_length_kind_of_type OCTET_STRING
  `and_then_kind`
  weak_kind_of_type OCTET_STRING

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
noextract
let synth_asn1_octet_string_V
  (tag: (the_asn1_type OCTET_STRING & asn1_value_int32_of_type OCTET_STRING))
  (value: datatype_of_asn1_type OCTET_STRING { v (dfst value) == v (snd tag) })
: GTot (refine_with_tag parser_tag_of_octet_string tag)
= value

/// Convert an `OCTET_STRING` value from the subtype used by its TLV parser to the subtype
/// used by its value parser/serializer
/// (value : subtype_{TLV}) <: subtype_{value}
noextract
let synth_asn1_octet_string_V_inverse
  (tag: (the_asn1_type OCTET_STRING & asn1_value_int32_of_type OCTET_STRING))
  (value': refine_with_tag parser_tag_of_octet_string tag)
: GTot (value: datatype_of_asn1_type OCTET_STRING { v (dfst value) == v (snd tag) /\ value' == synth_asn1_octet_string_V tag value})
= value'


///
/// Aux parser
///
noextract
let parse_asn1_octet_string_V
  (tag: (the_asn1_type OCTET_STRING & asn1_value_int32_of_type OCTET_STRING))
: parser (weak_kind_of_type OCTET_STRING) (refine_with_tag parser_tag_of_octet_string tag)
= weak_kind_of_type OCTET_STRING
  `weaken`
  parse_asn1_octet_string (v (snd tag))
  `parse_synth`
  synth_asn1_octet_string_V tag

///
/// Aux serializer
///
noextract
let serialize_asn1_octet_string_V
  (tag: (the_asn1_type OCTET_STRING & asn1_value_int32_of_type OCTET_STRING))
: serializer (parse_asn1_octet_string_V tag)
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
noextract
let parse_asn1_octet_string_V_unfold
  (tag: (the_asn1_type OCTET_STRING & asn1_value_int32_of_type OCTET_STRING))
  (input: bytes)
: Lemma (
  parse (parse_asn1_octet_string_V tag) input ==
 (match parse (parse_asn1_octet_string (v (snd tag))) input with
  | None -> None
  | Some (value, consumed) ->  Some (synth_asn1_octet_string_V tag value, consumed)))
= parse_synth_eq
  (* p1 *) (weak_kind_of_type OCTET_STRING
            `weaken`
            parse_asn1_octet_string (v (snd tag)))
  (* f2 *) (synth_asn1_octet_string_V tag)
  (* in *) input

/// Reveal the computation of serialzation
noextract
let serialize_asn1_octet_string_V_unfold
  (tag: (the_asn1_type OCTET_STRING & asn1_value_int32_of_type OCTET_STRING))
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
noextract
let parse_asn1_octet_string_TLV
: parser parse_asn1_octet_string_TLV_kind (datatype_of_asn1_type OCTET_STRING)
= parse_tagged_union
  (* pt *) (parse_asn1_tag_of_type OCTET_STRING
            `nondep_then`
            parse_asn1_length_of_type OCTET_STRING)
  (* tg *) (parser_tag_of_octet_string)
  (* p  *) (parse_asn1_octet_string_V)

///
/// Serializer
///
noextract
let serialize_asn1_octet_string_TLV
: serializer parse_asn1_octet_string_TLV
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
let parse_asn1_octet_string_TLV_unfold
  (input: bytes)
: Lemma (
  parse parse_asn1_octet_string_TLV input ==
 (match parse (parse_asn1_tag_of_type OCTET_STRING) input with
  | None -> None
  | Some (tag, consumed_tag) ->
    (let input_LV = Seq.slice input consumed_tag (Seq.length input) in
     match parse (parse_asn1_length_of_type OCTET_STRING) input_LV with
     | None -> None
     | Some (len, consumed_len) ->
       (let input_V = Seq.slice input_LV consumed_len (Seq.length input_LV) in
        match parse (parse_asn1_octet_string_V (tag, len)) input_V with
        | None -> None
        | Some (value, consumed_value) ->
               Some ((synth_asn1_octet_string_V (tag,len) value),
                     (consumed_tag + consumed_len + consumed_value <: consumed_length input)))
     ))
)
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
    parse_asn1_octet_string_V_unfold tag (Seq.slice input consumed (Seq.length input)) );

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
noextract
let serialize_asn1_octet_string_TLV_unfold
  (value: datatype_of_asn1_type OCTET_STRING)
: Lemma (
  serialize serialize_asn1_octet_string_TLV value ==
  serialize (serialize_asn1_tag_of_type OCTET_STRING) OCTET_STRING
  `Seq.append`
  serialize (serialize_asn1_length_of_type OCTET_STRING) (dfst value)
  `Seq.append`
  serialize (serialize_asn1_octet_string (v (dfst value))) value
)
= serialize_nondep_then_eq
  (* s1 *) (serialize_asn1_tag_of_type OCTET_STRING)
  (* s2 *) (serialize_asn1_length_of_type OCTET_STRING)
  (* in *) (parser_tag_of_octet_string value);
  serialize_asn1_octet_string_V_unfold (parser_tag_of_octet_string value) value;
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
noextract
let serialize_asn1_octet_string_TLV_size
  (value: datatype_of_asn1_type OCTET_STRING)
: Lemma (
  Seq.length (serialize serialize_asn1_octet_string_TLV value) ==
  1 + length_of_asn1_length (dfst value) + B32.length (dsnd value)
)
= serialize_asn1_octet_string_TLV_unfold value;
  serialize_asn1_tag_of_type_size OCTET_STRING OCTET_STRING;
  serialize_asn1_length_size (dfst value);
  serialize_asn1_length_of_type_eq OCTET_STRING (dfst value);
  serialize_asn1_octet_string_size (v (dfst value)) value
#pop-options

