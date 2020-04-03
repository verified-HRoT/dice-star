module ASN1.Spec.OCTET_STRING

open LowParse.Spec.Base
open LowParse.Spec.Combinators
open LowParse.Spec.SeqBytes.Base

open ASN1.Base
open ASN1.Spec.Tag
open ASN1.Spec.Length

open FStar.Integers

// let synth_asn1_octet_string
//   (l: asn1_length_t)
//   (ls: lbytes l)
// : GTot (x: datatype_of_asn1_type OCTET_STRING{v (dfst x) == l})
//   // (requires True)
//   // (ensures fun x -> v (dfst x) == l)
// = (|I.u l, ls|)

// let synth_asn1_octet_string_inverse
//   (l: asn1_length_t)
//   (x: datatype_of_asn1_type OCTET_STRING{v (dfst x) == l})
// : GTot (ls: lbytes l)
//   // (requires v (dfst x) == l)
//   // (ensures fun ls -> synth_asn1_octet_string l ls == x)
// = dsnd x

let parse_asn1_octet_string_kind (l: asn1_length_t) = total_constant_size_parser_kind l
let parse_asn1_octet_string
  (l: asn1_length_t)
// : parser (parse_asn1_octet_string_kind l) (x: datatype_of_asn1_type OCTET_STRING{v (dfst x) == l})
= parse_seq_flbytes l
//   `parse_synth`
//   synth_asn1_octet_string l

let serialize_asn1_octet_string
  (l: asn1_length_t)
= serialize_seq_flbytes l
// = serialize_synth
//   (* p1 *) (parse_seq_flbytes l)
//   (* f2 *) (synth_asn1_octet_string l)
  // (* s1 *) (serialize_seq_flbytes l)
//   (* g1 *) (synth_asn1_octet_string_inverse l)
//   (* Prf*) ()

let parse_asn1_octet_string_kind_weak = strong_parser_kind asn1_length_min asn1_length_max None
let parse_asn1_octet_string_weak
  (l: asn1_length_t)
: parser parse_asn1_octet_string_kind_weak _ //(datatype_of_asn1_type OCTET_STRING)
= (parse_asn1_octet_string_kind_weak
   `weaken`
   parse_asn1_octet_string l)

let serialize_asn1_octet_string_weak
  (l: asn1_length_t)
: serializer (parse_asn1_octet_string_weak l)
= (parse_asn1_octet_string_kind_weak
   `serialize_weaken`
   serialize_asn1_octet_string l)

/// Specialized TLV
///
// let synth_asn1_octet_string_L
//   (x: the_asn1_type OCTET_STRING & asn1_len_of_tag OCTET_STRING)
// : GTot (asn1_len_of_tag OCTET_STRING)
// = snd x

// let synth_asn1_octet_string_L_inverse
//   (len: asn1_len_of_tag OCTET_STRING)
// : GTot (x: (the_asn1_type OCTET_STRING & asn1_len_of_tag OCTET_STRING){len == synth_asn1_octet_string_L x})
// = (OCTET_STRING, len)

let parser_tag_of_octet_string
  (x: datatype_of_asn1_type OCTET_STRING)
: GTot (the_asn1_type OCTET_STRING & asn1_int32_of_tag OCTET_STRING)
= (OCTET_STRING, dfst x)

let synth_asn1_octet_string_data
  (len: asn1_int32_of_tag OCTET_STRING)
  (x: the_asn1_type OCTET_STRING & asn1_int32_of_tag OCTET_STRING{x == (OCTET_STRING, len)})
  (s: lbytes (v len))
: GTot (refine_with_tag parser_tag_of_octet_string x)
= let value: datatype_of_asn1_type OCTET_STRING = (|len, s|) in
  let y: refine_with_tag parser_tag_of_octet_string x = value in
  y

let synth_asn1_octet_string_data_inverse
  (len: asn1_int32_of_tag OCTET_STRING)
  (x: the_asn1_type OCTET_STRING & asn1_int32_of_tag OCTET_STRING{x == (OCTET_STRING, len)})
  (value: refine_with_tag parser_tag_of_octet_string x)
: GTot (s: lbytes (v len))
= dsnd
    #(asn1_int32_of_tag OCTET_STRING)
    #(fun (len:asn1_int32_of_tag OCTET_STRING) -> s:bytes{Seq.length s == v len})
    value

let parse_asn1_octet_string_kind_strong
  (x: the_asn1_type OCTET_STRING & asn1_int32_of_tag OCTET_STRING)
: parser_kind
= total_constant_size_parser_kind (v (snd x))

let parse_asn1_octet_string_data
  (x: the_asn1_type OCTET_STRING & asn1_int32_of_tag OCTET_STRING)
: Tot (parser (parse_asn1_octet_string_kind_strong x) (refine_with_tag parser_tag_of_octet_string x))
= parse_asn1_octet_string (v (snd x))
  `parse_synth`
  synth_asn1_octet_string_data (snd x) x

let parse_asn1_octet_string_data_unfold
  (input: bytes)
: Lemma (
  forall (x: the_asn1_type OCTET_STRING & asn1_int32_of_tag OCTET_STRING).
)

let serialize_asn1_octet_string_data
  (x: the_asn1_type OCTET_STRING & asn1_int32_of_tag OCTET_STRING)
: Tot (serializer (parse_asn1_octet_string_data x))
= serialize_synth
  (* p1 *) (parse_asn1_octet_string (v (snd x)))
  (* f2 *) (synth_asn1_octet_string_data (snd x) x)
  (* s1 *) (serialize_asn1_octet_string (v (snd x)))
  (* g1 *) (synth_asn1_octet_string_data_inverse (snd x) x)
  (* Prf*) ()

let parse_asn1_octet_string_data_weak
  (x: the_asn1_type OCTET_STRING & asn1_int32_of_tag OCTET_STRING)
: Tot (parser parse_asn1_octet_string_kind_weak (refine_with_tag parser_tag_of_octet_string x))
= parse_asn1_octet_string_kind_weak
  `weaken`
  parse_asn1_octet_string_data x

let serialize_asn1_octet_string_data_weak
  (x: the_asn1_type OCTET_STRING & asn1_int32_of_tag OCTET_STRING)
: Tot (serializer (parse_asn1_octet_string_data_weak x))
= parse_asn1_octet_string_kind_weak
  `serialize_weaken`
  serialize_asn1_octet_string_data x

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
  parse_asn1_length_kind_of_tag OCTET_STRING
  `and_then_kind`
  parse_asn1_octet_string_kind_weak

let parse_asn1_octet_string_TLV
: parser parse_asn1_octet_string_TLV_kind (datatype_of_asn1_type OCTET_STRING)
= parse_tagged_union
  (* pt *) (parse_the_asn1_tag OCTET_STRING
            `nondep_then`
            parse_asn1_length_of_tag OCTET_STRING)
  (* tg *) (parser_tag_of_octet_string)
  (* p  *) (parse_asn1_octet_string_data_weak)

let parse_asn1_octet_string_TLV_unfold
  (input: bytes)
: Lemma (
  parse parse_asn1_octet_string_TLV input ==
 (match parse (parse_the_asn1_tag OCTET_STRING) input with
  | None -> None
  | Some (v_T, l_T) ->
    (let input_LV = Seq.slice input l_T (Seq.length input) in
     match parse (parse_asn1_length_of_tag OCTET_STRING) input_LV with
     | None -> None
     | Some (v_L, l_L) ->
       (let input_data = Seq.slice input_LV l_L (Seq.length input_LV) in
        match parse (parse_asn1_octet_string_data (v_T, v_L)) input_data with
        | None -> None
        | Some (v_V, l_V) -> Some (v_V, (l_T + l_L + l_V <: consumed_length input)))
     ))
)
= nondep_then_eq
  (* p1 *) (parse_the_asn1_tag OCTET_STRING)
  (* p2 *) (parse_asn1_length_of_tag OCTET_STRING)
  (* in *) (input);
  parse_synth_eq
  (* p1 *) (parse_asn1_octet_string (v (snd x)))
  (* f2 *) (synth_asn1_octet_string_data)
  (* in *)

let serialize_asn1_octet_string_TLV
: serializer parse_asn1_octet_string_TLV
= serialize_tagged_union
  (* st *) (serialize_the_asn1_tag OCTET_STRING
            `serialize_nondep_then`
            serialize_asn1_length_of_tag OCTET_STRING)
  (* tg *) (parser_tag_of_octet_string)
  (* s  *) (serialize_asn1_octet_string_data_weak)

let length_lemma
  (input: bytes)
: Lemma
  (requires (Some? (parse parse_asn1_octet_string_TLV input)))
  (ensures (
    let px = parse parse_asn1_octet_string_TLV input in
    let pt = parse (parse_the_asn1_tag OCTET_STRING) input in
    let pl = parse (parse_asn1_length_of_tag OCTET_STRING) (Seq.slice input 0 )
  ))
