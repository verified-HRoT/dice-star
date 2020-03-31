module ASN1.Spec.OCTET_STRING

open LowParse.Spec.Base
open LowParse.Spec.Combinators
open LowParse.Spec.SeqBytes.Base

open ASN1.Base
open ASN1.Spec.Tag
open ASN1.Spec.Length

module I = FStar.Integers

// let synth_asn1_octet_string
//   (l: asn1_length_t)
//   (ls: lbytes l)
// : GTot (x: datatype_of_asn1_type OCTET_STRING{I.v (dfst x) == l})
//   // (requires True)
//   // (ensures fun x -> I.v (dfst x) == l)
// = (|I.u l, ls|)

// let synth_asn1_octet_string_inverse
//   (l: asn1_length_t)
//   (x: datatype_of_asn1_type OCTET_STRING{I.v (dfst x) == l})
// : GTot (ls: lbytes l)
//   // (requires I.v (dfst x) == l)
//   // (ensures fun ls -> synth_asn1_octet_string l ls == x)
// = dsnd x

let parse_asn1_octet_string_kind (l: asn1_length_t) = total_constant_size_parser_kind l
let parse_asn1_octet_string
  (l: asn1_length_t)
// : parser (parse_asn1_octet_string_kind l) (x: datatype_of_asn1_type OCTET_STRING{I.v (dfst x) == l})
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
let synth_asn1_octet_string_L
  (x: the_asn1_type OCTET_STRING * asn1_len_of_tag OCTET_STRING)
: GTot (asn1_len_of_tag OCTET_STRING)
= snd x

let synth_asn1_octet_string_L_inverse
  (len: asn1_len_of_tag OCTET_STRING)
: GTot (x: (the_asn1_type OCTET_STRING * asn1_len_of_tag OCTET_STRING){len == synth_asn1_octet_string_L x})
= (OCTET_STRING, len)

let parser_tag_of_octet_string
  (x: datatype_of_asn1_type OCTET_STRING)
: (len: asn1_len_of_tag OCTET_STRING)
= dfst x

let synth_asn1_octet_string_V
  (len: asn1_len_of_tag OCTET_STRING)
  (x: lbytes (I.v len))
: GTot (refine_with_tag parser_tag_of_octet_string len)
= (|len, x|)

let synth_asn1_octet_string_V_inverse
  (len: asn1_len_of_tag OCTET_STRING)
  (x: datatype_of_asn1_type OCTET_STRING)
: GTot (x: datatype_of_asn1_type OCTET_STRING{I.v (dfst x) == I.v len})
= x

// let parse_asn1_octet_string_TLV_kind
// = parse_asn1_tag_kind
//   `and_then_kind`
//   parse_asn1_length_kind
//   `and_then_kind`
//   strong_parser_kind asn1_length_min asn1_length_max None

let parse_asn1_octet_string_TLV
: parser _ (datatype_of_asn1_type OCTET_STRING)
= ((parse_the_asn1_tag OCTET_STRING
  `nondep_then`
  parse_asn1_length_of_tag OCTET_STRING
  `parse_synth`
  synth_asn1_octet_string_L)
  `and_then`
  parse_asn1_octet_string_weak)
  `parse_synth`
  synth_asn1_octet_string_V

let serialize_asn1_octet_string_TLV
: serializer parse_asn1_octet_string_TLV
= serialize_synth
  (* p1 *) (parse_the_asn1_tag OCTET_STRING
            `nondep_then`
            parse_asn1_length_of_tag OCTET_STRING
            `nondep_then`
            parse_asn1_octet_string)
  (* f2 *) (synth_asn1_octet_string_TLV)
  (* s1 *) (serialize_the_asn1_tag OCTET_STRING
            `serialize_nondep_then`
            serialize_asn1_length_of_tag OCTET_STRING
            `serialize_nondep_then`
            serialize_asn1_octet_string)
  (* g1 *) (synth_asn1_octet_string_TLV_inverse)
  (* Prf*) ()

