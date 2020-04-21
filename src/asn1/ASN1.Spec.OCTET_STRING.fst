module ASN1.Spec.OCTET_STRING

open LowParse.Spec.Base
open LowParse.Spec.Combinators
// open LowParse.Spec.Bytes
open LowParse.Spec.SeqBytes.Base

open ASN1.Base
open ASN1.Spec.Tag
open ASN1.Spec.Length

open FStar.Integers

let synth_asn1_octet_string
  (l: asn1_length_of_type OCTET_STRING)
  (ls: lbytes l)
: GTot (value: datatype_of_asn1_type OCTET_STRING{v (dfst value) == l})
= (|u l, ls|)

let synth_asn1_octet_string_inverse
  (l: asn1_length_of_type OCTET_STRING)
  (value: datatype_of_asn1_type OCTET_STRING{v (dfst value) == l})
: GTot (ls: lbytes l{ value == synth_asn1_octet_string l ls })
= dsnd value

let parse_asn1_octet_string_kind (l: asn1_length_of_type OCTET_STRING) = total_constant_size_parser_kind l
let parse_asn1_octet_string
  (l: asn1_length_of_type OCTET_STRING)
: parser (parse_asn1_octet_string_kind l) (x: datatype_of_asn1_type OCTET_STRING{v (dfst x) == l})
= parse_seq_flbytes l
  `parse_synth`
 synth_asn1_octet_string l

let parse_asn1_octet_string_unfold
  (l: asn1_length_of_type OCTET_STRING)
  (input: bytes)
: Lemma (
  parse (parse_asn1_octet_string l) input ==
 (match parse (parse_seq_flbytes l) input with
  | None -> None
  | Some (ls, consumed) -> Some (synth_asn1_octet_string l ls, consumed)))
= parse_synth_eq
  (* p1 *) (parse_seq_flbytes l)
  (* f2 *) (synth_asn1_octet_string l)
  (* in *) (input)

let serialize_asn1_octet_string
  (l: asn1_length_of_type OCTET_STRING)
: serializer (parse_asn1_octet_string l)
= serialize_synth
  (* p1 *) (parse_seq_flbytes l)
  (* f2 *) (synth_asn1_octet_string l)
  (* s1 *) (serialize_seq_flbytes l)
  (* g1 *) (synth_asn1_octet_string_inverse l)
  (* Prf*) ()

let serialize_asn1_octet_string_unfold
  (l: asn1_length_of_type OCTET_STRING)
  (value: datatype_of_asn1_type OCTET_STRING{v (dfst value) == l})
: Lemma (
  serialize (serialize_asn1_octet_string l) value ==
  serialize (serialize_seq_flbytes l) (synth_asn1_octet_string_inverse l value))
= serialize_synth_eq
  (* p1 *) (parse_seq_flbytes l)
  (* f2 *) (synth_asn1_octet_string l)
  (* s1 *) (serialize_seq_flbytes l)
  (* g1 *) (synth_asn1_octet_string_inverse l)
  (* Prf*) ()
  (* in *) (value)

let parse_asn1_octet_string_weak
  (l: asn1_length_of_type OCTET_STRING)
: parser (weak_kind_of_type SEQUENCE) (value: datatype_of_asn1_type OCTET_STRING{v (dfst value) == l})
= weak_kind_of_type SEQUENCE
  `weaken`
  parse_asn1_octet_string l

let serialize_asn1_octet_string_weak
  (l: asn1_length_of_type OCTET_STRING)
: serializer (parse_asn1_octet_string_weak l)
= weak_kind_of_type SEQUENCE
  `serialize_weaken`
  serialize_asn1_octet_string l

/// Specialized TLV
///
// let synth_asn1_octet_string_L
//   (x: the_asn1_type OCTET_STRING & asn1_len_of_type OCTET_STRING)
// : GTot (asn1_len_of_type OCTET_STRING)
// = snd x

// let synth_asn1_octet_string_L_inverse
//   (len: asn1_len_of_type OCTET_STRING)
// : GTot (x: (the_asn1_type OCTET_STRING & asn1_len_of_type OCTET_STRING){len == synth_asn1_octet_string_L x})
// = (OCTET_STRING, len)

let parser_tag_of_octet_string
  (x: datatype_of_asn1_type OCTET_STRING)
: GTot (the_asn1_type OCTET_STRING & asn1_int32_of_type OCTET_STRING)
= (OCTET_STRING, dfst x)

// let synth_asn1_octet_string_data
//   (len: asn1_int32_of_type OCTET_STRING)
//   (x: the_asn1_type OCTET_STRING & asn1_int32_of_type OCTET_STRING{x == (OCTET_STRING, len)})
//   (s: lbytes (v len))
// : GTot (refine_with_tag parser_tag_of_octet_string x)
// = let value: datatype_of_asn1_type OCTET_STRING = (|len, s|) in
//   let y: refine_with_tag parser_tag_of_octet_string x = value in
//   y

// let synth_asn1_octet_string_data_inverse
//   (len: asn1_int32_of_type OCTET_STRING)
//   (x: the_asn1_type OCTET_STRING & asn1_int32_of_type OCTET_STRING{x == (OCTET_STRING, len)})
//   (value: refine_with_tag parser_tag_of_octet_string x)
// : GTot (s: lbytes (v len))
// = dsnd
//     #(asn1_int32_of_type OCTET_STRING)
//     #(fun (len:asn1_int32_of_type OCTET_STRING) -> s:bytes{Seq.length s == v len})
//     value

// let parse_asn1_octet_string_kind_strong
//   (x: the_asn1_type OCTET_STRING & asn1_int32_of_type OCTET_STRING)
// : parser_kind
// = total_constant_size_parser_kind (v (snd x))

// let parse_asn1_octet_string_data
//   (x: the_asn1_type OCTET_STRING & asn1_int32_of_type OCTET_STRING)
// : Tot (parser (parse_asn1_octet_string_kind_strong x) (refine_with_tag parser_tag_of_octet_string x))
// = parse_asn1_octet_string (v (snd x))
//   `parse_synth`
//   synth_asn1_octet_string_data (snd x) x

// let serialize_asn1_octet_string_data
//   (x: the_asn1_type OCTET_STRING & asn1_int32_of_type OCTET_STRING)
// : Tot (serializer (parse_asn1_octet_string_data x))
// = serialize_synth
//   (* p1 *) (parse_asn1_octet_string (v (snd x)))
//   (* f2 *) (synth_asn1_octet_string_data (snd x) x)
//   (* s1 *) (serialize_asn1_octet_string (v (snd x)))
//   (* g1 *) (synth_asn1_octet_string_data_inverse (snd x) x)
//   (* Prf*) ()

// let parse_asn1_octet_string_data_weak
//   (x: the_asn1_type OCTET_STRING & asn1_int32_of_type OCTET_STRING)
// : Tot (parser parse_asn1_octet_string_kind_weak (refine_with_tag parser_tag_of_octet_string x))
// = parse_asn1_octet_string_kind_weak
//   `weaken`
//   parse_asn1_octet_string_data x

// let serialize_asn1_octet_string_data_weak
//   (x: the_asn1_type OCTET_STRING & asn1_int32_of_type OCTET_STRING)
// : Tot (serializer (parse_asn1_octet_string_data_weak x))
// = parse_asn1_octet_string_kind_weak
//   `serialize_weaken`
//   serialize_asn1_octet_string_data x

// let parse_asn1_octet_string_TLV_kind
// = parse_asn1_tag_kind
//   `and_then_kind`
//   parse_asn1_length_kind
//   `and_then_kind`
//   strong_parser_kind asn1_length_min asn1_length_max None

let parse_asn1_octet_string_TLV_kind
: parser_kind
= parse_asn1_tag_kind
  `and_then_kind`
  parse_asn1_length_kind_of_type OCTET_STRING
  `and_then_kind`
  weak_kind_of_type SEQUENCE

let synth_asn1_octet_string_V
  (tag: (the_asn1_type OCTET_STRING & asn1_int32_of_type OCTET_STRING))
  (value: datatype_of_asn1_type OCTET_STRING { v (dfst value) == v (snd tag) })
: GTot (value': refine_with_tag parser_tag_of_octet_string tag)
= value

let synth_asn1_octet_string_V_inverse
  (tag: (the_asn1_type OCTET_STRING & asn1_int32_of_type OCTET_STRING))
  (value': refine_with_tag parser_tag_of_octet_string tag)
: GTot (value: datatype_of_asn1_type OCTET_STRING { v (dfst value) == v (snd tag) /\ value' == synth_asn1_octet_string_V tag value})
= value'

let parse_asn1_octet_string_V
  (tag: (the_asn1_type OCTET_STRING & asn1_int32_of_type OCTET_STRING))
: parser (weak_kind_of_type SEQUENCE) (refine_with_tag parser_tag_of_octet_string tag)
= parse_asn1_octet_string_weak (v (snd tag))
  `parse_synth`
  synth_asn1_octet_string_V tag

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

let serialize_asn1_octet_string_V
  (tag: (the_asn1_type OCTET_STRING & asn1_int32_of_type OCTET_STRING))
: serializer (parse_asn1_octet_string_V tag)
= serialize_synth
  (* p1 *) (parse_asn1_octet_string_weak (v (snd tag)))
  (* f2 *) (synth_asn1_octet_string_V tag)
  (* s1 *) (serialize_asn1_octet_string_weak (v (snd tag)))
  (* g1 *) (synth_asn1_octet_string_V_inverse tag)
  (* prf*) ()

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

let parse_asn1_octet_string_TLV
: parser parse_asn1_octet_string_TLV_kind (datatype_of_asn1_type OCTET_STRING)
= parse_tagged_union
  (* pt *) (parse_the_asn1_tag OCTET_STRING
            `nondep_then`
            parse_asn1_length_of_type OCTET_STRING)
  (* tg *) (parser_tag_of_octet_string)
  (* p  *) (parse_asn1_octet_string_V)

#restart-solver
#push-options "--query_stats --z3rlimit 32 --initial_ifuel 8"
let parse_asn1_octet_string_TLV_unfold
  (input: bytes)
: Lemma (
  parse parse_asn1_octet_string_TLV input ==
 (match parse (parse_the_asn1_tag OCTET_STRING) input with
  | None -> None
  | Some (tag, consumed_tag) ->
    (let input_LV = Seq.slice input consumed_tag (Seq.length input) in
     match parse (parse_asn1_length_of_type OCTET_STRING) input_LV with
     | None -> None
     | Some (len, consumed_len) ->
       (let input_V = Seq.slice input_LV consumed_len (Seq.length input_LV) in
        match parse (parse_asn1_octet_string_V (tag, len)) input_V with
        | None -> None
        | Some (value, consumed_value) -> Some (value, (consumed_tag + consumed_len + consumed_value <: consumed_length input)))
     ))
)
= nondep_then_eq
  (* p1 *) (parse_the_asn1_tag OCTET_STRING)
  (* p2 *) (parse_asn1_length_of_type OCTET_STRING)
  (* in *) (input);

  let parsed_tag
  = parse (parse_the_asn1_tag OCTET_STRING
           `nondep_then`
           parse_asn1_length_of_type OCTET_STRING) input in
  if (Some? parsed_tag) then
  ( let Some (tag, consumed) = parsed_tag in
    parse_asn1_octet_string_V_unfold tag (Seq.slice input consumed (Seq.length input)) );

  parse_tagged_union_eq
  (* pt *) (parse_the_asn1_tag OCTET_STRING
            `nondep_then`
            parse_asn1_length_of_type OCTET_STRING)
  (* tg *) (parser_tag_of_octet_string)
  (* p  *) (fun tag -> parse_asn1_octet_string_V_unfold tag input;
                     parse_asn1_octet_string_V tag)
  (* in *) (input)

#pop-options

let serialize_asn1_octet_string_TLV
: serializer parse_asn1_octet_string_TLV
= serialize_tagged_union
  (* st *) (serialize_the_asn1_tag OCTET_STRING
            `serialize_nondep_then`
            serialize_asn1_length_of_type OCTET_STRING)
  (* tg *) (parser_tag_of_octet_string)
  (* s  *) (serialize_asn1_octet_string_V)
  // (* s  *) (fun (tag: (the_asn1_type OCTET_STRING & asn1_int32_of_type OCTET_STRING))
  //           -> serialize_synth
  //              (* p1 *) (parse_asn1_octet_string_weak (v (snd tag)))
  //              (* f2 *) (fun value -> value <: refine_with_tag parser_tag_of_octet_string tag)
  //              (* s1 *) (serialize_asn1_octet_string_weak (v (snd tag)))
  //              (* g1 *) (fun value -> value <: value: datatype_of_asn1_type OCTET_STRING{v (dfst value) == v (snd tag)})
  //              (* prf*) ())

#push-options "--query_stats --z3rlimit 32"
let serialize_asn1_octet_string_TLV_unfold
  (value: datatype_of_asn1_type OCTET_STRING)
: Lemma (
  serialize serialize_asn1_octet_string_TLV value ==
  serialize (serialize_the_asn1_tag OCTET_STRING) OCTET_STRING
  `Seq.append`
  serialize (serialize_asn1_length_of_type OCTET_STRING) (dfst value)
  `Seq.append`
  serialize (serialize_asn1_octet_string_weak (v (dfst value))) value
)
= serialize_nondep_then_eq
  (* s1 *) (serialize_the_asn1_tag OCTET_STRING)
  (* s2 *) (serialize_asn1_length_of_type OCTET_STRING)
  (* in *) (parser_tag_of_octet_string value);
  serialize_asn1_octet_string_V_unfold (parser_tag_of_octet_string value) value;
  serialize_tagged_union_eq
  (* st *) (serialize_the_asn1_tag OCTET_STRING
            `serialize_nondep_then`
            serialize_asn1_length_of_type OCTET_STRING)
  (* tg *) (parser_tag_of_octet_string)
  (* s  *) (serialize_asn1_octet_string_V)
  (* in *) (value)
#pop-options

private
let length_test
  (value: datatype_of_asn1_type OCTET_STRING)
: Lemma (
  let (|len, s|) = value in
  v len == Seq.length (serialize (serialize_asn1_octet_string (v (snd (parser_tag_of_octet_string value)))) value)
)
= let tag = parser_tag_of_octet_string value in
  let l = v (snd tag) in
  parser_kind_prop_equiv
  (* k *) (parse_asn1_octet_string_kind l)
  (* p *) (parse_asn1_octet_string l);
  serialize_asn1_octet_string_unfold l value
