module ASN1.Spec.OCTET_STRING

open LowParse.Spec.Base
open LowParse.Spec.Combinators
open LowParse.Spec.Bytes

open ASN1.Base
open ASN1.Spec.Tag
open ASN1.Spec.Length

open FStar.Integers

module B32 = FStar.Bytes

noextract
let synth_asn1_octet_string
  (l: asn1_length_of_type OCTET_STRING)
  (s32: B32.lbytes l)
: GTot (value: datatype_of_asn1_type OCTET_STRING{v (dfst value) == l})
= (|u l, s32|)

noextract
let synth_asn1_octet_string_inverse
  (l: asn1_length_of_type OCTET_STRING)
  (value: datatype_of_asn1_type OCTET_STRING{v (dfst value) == l})
: GTot (s32: B32.lbytes l{ value == synth_asn1_octet_string l s32 })
= dsnd value

noextract
let parse_asn1_octet_string_kind (l: asn1_length_of_type OCTET_STRING) = total_constant_size_parser_kind l

noextract
let parse_asn1_octet_string
  (l: asn1_length_of_type OCTET_STRING)
: parser (parse_asn1_octet_string_kind l) (x: datatype_of_asn1_type OCTET_STRING{v (dfst x) == l})
= parse_flbytes l
  `parse_synth`
  synth_asn1_octet_string l

noextract
let parse_asn1_octet_string_unfold
  (l: asn1_length_of_type OCTET_STRING)
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

noextract
let serialize_asn1_octet_string
  (l: asn1_length_of_type OCTET_STRING)
: serializer (parse_asn1_octet_string l)
= serialize_synth
  (* p1 *) (parse_flbytes l)
  (* f2 *) (synth_asn1_octet_string l)
  (* s1 *) (serialize_flbytes l)
  (* g1 *) (synth_asn1_octet_string_inverse l)
  (* Prf*) ()

noextract
let serialize_asn1_octet_string_unfold
  (l: asn1_length_of_type OCTET_STRING)
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

noextract
let serialize_asn1_octet_string_size
  (l: asn1_length_of_type OCTET_STRING)
  (value: datatype_of_asn1_type OCTET_STRING{v (dfst value) == l})
: Lemma (
  Seq.length (serialize (serialize_asn1_octet_string l) value) == l)
= parser_kind_prop_equiv (parse_asn1_octet_string_kind l) (parse_asn1_octet_string l);
  serialize_asn1_octet_string_unfold l value

noextract
let parse_asn1_octet_string_weak
  (l: asn1_length_of_type OCTET_STRING)
: parser (weak_kind_of_type SEQUENCE) (value: datatype_of_asn1_type OCTET_STRING{v (dfst value) == l})
= weak_kind_of_type SEQUENCE
  `weaken`
  parse_asn1_octet_string l

noextract
let serialize_asn1_octet_string_weak
  (l: asn1_length_of_type OCTET_STRING)
: serializer (parse_asn1_octet_string_weak l)
= weak_kind_of_type SEQUENCE
  `serialize_weaken`
  serialize_asn1_octet_string l

/// Specialized TLV
///
noextract
let parser_tag_of_octet_string
  (x: datatype_of_asn1_type OCTET_STRING)
: GTot (the_asn1_type OCTET_STRING & asn1_int32_of_type OCTET_STRING)
= (OCTET_STRING, dfst x)

noextract
let parse_asn1_octet_string_TLV_kind
: parser_kind
= parse_asn1_tag_kind
  `and_then_kind`
  parse_asn1_length_kind_of_type OCTET_STRING
  `and_then_kind`
  weak_kind_of_type OCTET_STRING


////////// V //////////
(* NOTE: Have this aux parser explicitly defined will make the proofs simpler *)
noextract
let synth_asn1_octet_string_V
  (tag: (the_asn1_type OCTET_STRING & asn1_int32_of_type OCTET_STRING))
  (value: datatype_of_asn1_type OCTET_STRING { v (dfst value) == v (snd tag) })
: GTot (refine_with_tag parser_tag_of_octet_string tag)
= value

noextract
let synth_asn1_octet_string_V_inverse
  (tag: (the_asn1_type OCTET_STRING & asn1_int32_of_type OCTET_STRING))
  (value': refine_with_tag parser_tag_of_octet_string tag)
: GTot (value: datatype_of_asn1_type OCTET_STRING { v (dfst value) == v (snd tag) /\ value' == synth_asn1_octet_string_V tag value})
= value'

noextract
let parse_asn1_octet_string_V
  (tag: (the_asn1_type OCTET_STRING & asn1_int32_of_type OCTET_STRING))
: parser (weak_kind_of_type OCTET_STRING) (refine_with_tag parser_tag_of_octet_string tag)
= parse_asn1_octet_string_weak (v (snd tag))
  `parse_synth`
  synth_asn1_octet_string_V tag

noextract
let parse_asn1_octet_string_V_unfold
  (tag: (the_asn1_type OCTET_STRING & asn1_int32_of_type OCTET_STRING))
  (input: bytes)
: Lemma (
  parse (parse_asn1_octet_string_V tag) input ==
 (match parse (parse_asn1_octet_string (v (snd tag))) input with
  | None -> None
  | Some (value, consumed) ->  Some (synth_asn1_octet_string_V tag value, consumed)))
= parse_synth_eq
  (* p1 *) (parse_asn1_octet_string_weak (v (snd tag)))
  (* f2 *) (synth_asn1_octet_string_V tag)
  (* in *) input

noextract
let serialize_asn1_octet_string_V
  (tag: (the_asn1_type OCTET_STRING & asn1_int32_of_type OCTET_STRING))
: serializer (parse_asn1_octet_string_V tag)
= serialize_synth
  (* p1 *) (parse_asn1_octet_string_weak (v (snd tag)))
  (* f2 *) (synth_asn1_octet_string_V tag)
  (* s1 *) (serialize_asn1_octet_string_weak (v (snd tag)))
  (* g1 *) (synth_asn1_octet_string_V_inverse tag)
  (* prf*) ()

noextract
let serialize_asn1_octet_string_V_unfold
  (tag: (the_asn1_type OCTET_STRING & asn1_int32_of_type OCTET_STRING))
  (value: refine_with_tag parser_tag_of_octet_string tag)
: Lemma (
  serialize (serialize_asn1_octet_string_V tag) value ==
  serialize (serialize_asn1_octet_string (v (snd tag))) value
)
= serialize_synth_eq
  (* p1 *) (parse_asn1_octet_string_weak (v (snd tag)))
  (* f2 *) (synth_asn1_octet_string_V tag)
  (* s1 *) (serialize_asn1_octet_string_weak (v (snd tag)))
  (* g1 *) (synth_asn1_octet_string_V_inverse tag)
  (* prf*) ()
  (* in *) (value)

////////////////////////////////////////////////////////////
noextract
let parse_asn1_octet_string_TLV
: parser parse_asn1_octet_string_TLV_kind (datatype_of_asn1_type OCTET_STRING)
= parse_tagged_union
  (* pt *) (parse_asn1_tag_of_type OCTET_STRING
            `nondep_then`
            parse_asn1_length_of_type OCTET_STRING)
  (* tg *) (parser_tag_of_octet_string)
  (* p  *) (parse_asn1_octet_string_V)

#restart-solver
#push-options "--query_stats --z3rlimit 32 --initial_ifuel 8"
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

noextract
let serialize_asn1_octet_string_TLV
: serializer parse_asn1_octet_string_TLV
= serialize_tagged_union
  (* st *) (serialize_asn1_tag_of_type OCTET_STRING
            `serialize_nondep_then`
            serialize_asn1_length_of_type OCTET_STRING)
  (* tg *) (parser_tag_of_octet_string)
  (* s  *) (serialize_asn1_octet_string_V)

#push-options "--query_stats --z3rlimit 32"
noextract
let serialize_asn1_octet_string_TLV_unfold
  (value: datatype_of_asn1_type OCTET_STRING)
: Lemma (
  serialize serialize_asn1_octet_string_TLV value ==
  serialize (serialize_asn1_tag_of_type OCTET_STRING) OCTET_STRING
  `Seq.append`
  serialize (serialize_asn1_length_of_type OCTET_STRING) (dfst value)
  `Seq.append`
  serialize (serialize_asn1_octet_string_weak (v (dfst value))) value
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

#push-options "--query_stats --z3rlimit 16"
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

