module RIoT.X509.AliasKeyTBS.Extensions

open ASN1.Spec
open ASN1.Low
open X509
include RIoT.X509.Base
include RIoT.X509.FWID
include RIoT.X509.CompositeDeviceID
include RIoT.X509.Extension
open FStar.Integers

module B32 = FStar.Bytes

open LowParse.Spec.SeqBytes.Base
open LowParse.Spec.Bytes

(*)
unfold let elem_t: Type = (t:Type & t)

let parser_kind_strong = k: parser_kind {Mkparser_kind'?.parser_kind_subkind k == Some ParserStrong}

let ser_t: Type
= ( k: parser_kind_strong &
    t: Type &
    p: parser k t &
    s: serializer p )

let wrap
  (#k: parser_kind_strong)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
: Tot (ser_t)
= (|k, t, p, s|)

let ser_list_t: Type = l: list ser_t { 0 < List.length l /\ List.length l <= 5}

let rec sequence_t
  (l: ser_list_t)
: Tot (Type)
  (decreases (List.length l))
= let l', (|k, t, p, s|) = List.Tot.Base.unsnoc l in
  List.Tot.Properties.lemma_unsnoc_length l;
  match l' with
  | [] -> ( t )
  | _  -> ( (sequence_t l' `tuple2` t) )

let rec parse_sequence_kind
  (l: ser_list_t)
: Tot (parser_kind_strong)
  (decreases (List.length l))
= let l', (|k, t, p, s|) = List.Tot.Base.unsnoc l in
  List.Tot.Properties.lemma_unsnoc_length l;
  match l' with
  | [] -> ( k )
  | _  -> ( (parse_sequence_kind l' `and_then_kind` k) )

let rec parse_sequence
  (l: ser_list_t)
: Tot (parser (parse_sequence_kind l) (sequence_t l))
  (decreases (List.length l))
= let l', (|k, t, p, s|) = List.Tot.Base.unsnoc l in
  List.Tot.Properties.lemma_unsnoc_length l;
  match l' with
  | [] -> ( p )
  | _  -> ( (parse_sequence l' `nondep_then` p) )

let rec serialize_sequence
  (l: ser_list_t)
: Tot (serializer (parse_sequence l))
  (decreases (List.length l))
= let l', (|k, t, p, s|) = List.Tot.Base.unsnoc l in
  List.Tot.Properties.lemma_unsnoc_length l;
  match l' with
  | [] -> ( s )
  | _  -> ( (serialize_sequence l' `serialize_nondep_then` s) )

(* Test Zone *)
let l: ser_list_t = [wrap serialize_asn1_integer_TLV;
                     wrap serialize_asn1_bit_string_TLV]

let msg_t: Type = (t: Type & x: t)

let msg_list_t: Type = l: list msg_t { 0 < List.length l /\ List.length l <= 5}

let wrap_msg
  (#t: Type)
  (x: t)
: Tot (msg_t)
= (|t, x|)

let rec msg_list_to_tuple_t
  (l: msg_list_t)
: Tot (Type)
  (decreases (List.length l))
= let l', (|t, x|) = List.Tot.Base.unsnoc l in
  List.Tot.Properties.lemma_unsnoc_length l;
  match l' with
  | [] -> ( t )
  | _  -> ( msg_list_to_tuple_t l' `tuple2` t )

let rec msg_list_to_tuple
  (l: msg_list_t)
: Tot (msg_list_to_tuple_t l)
  (decreases (List.length l))
= let l', (|t, x|) = List.Tot.Base.unsnoc l in
  List.Tot.Properties.lemma_unsnoc_length l;
  match l' with
  | [] -> ( x )
  | _  -> ( (msg_list_to_tuple l', x) )

let x: msg_list_t = [wrap_msg 1ul; wrap_msg ({bs_len = 2ul; bs_unused_bits = 0ul; bs_s = B32.create 1ul 1uy})]

let p = parse_sequence l

let _ assert (get_parser_type p == msg_list_to_tuple_t x)



type aliasKeyTBS_extensions_t (template_len: asn1_int32) = {
  aliasKeyTBS_extension_riot: riot_extension_t;
  aliasKeyTBS_extensions_template: B32.lbytes32 template_len
}
