module ASN1.Spec.Tag

include LowParse.Spec.Base
include LowParse.Spec.Combinators
include LowParse.Spec.Int

include ASN1.Base

/// Generic
///
val filter_asn1_tag
  (b: byte)
: Ghost bool
  (requires True)
  (ensures fun r -> r == (b = 0x01uy || b = 0x04uy || b = 0x05uy || b = 0x30uy))

let valid_asn1_tag_byte = parse_filter_refine filter_asn1_tag

val synth_asn1_tag
  (b: parse_filter_refine filter_asn1_tag)
: Ghost asn1_type
  (requires True)
  (ensures fun a ->
    a == (match b with
          | 0x01uy -> BOOLEAN
          | 0x04uy -> OCTET_STRING
          | 0x05uy -> NULL
          | 0x30uy -> SEQUENCE))

val synth_asn1_tag_inverse
  (a: asn1_type)
: Ghost (b: parse_filter_refine filter_asn1_tag{a == synth_asn1_tag b})
  (requires True)
  (ensures fun b -> a == synth_asn1_tag b)

let parse_asn1_tag_kind = strong_parser_kind 1 1 None
val parse_asn1_tag
: parser parse_asn1_tag_kind asn1_type

val parse_asn1_tag_unfold
  (input: bytes)
: Lemma (
  parser_kind_prop parse_asn1_tag_kind parse_asn1_tag /\
  parse parse_asn1_tag input ==
 (match parse parse_u8 input with
  | Some (x, consumed) -> if filter_asn1_tag x then
                          ( Some (synth_asn1_tag x, consumed) )
                          else
                          ( None )
  | None -> None))

val serialize_asn1_tag
: serializer parse_asn1_tag

val serialize_asn1_tag_unfold
  (a: asn1_type)
: Lemma (
  serialize serialize_asn1_tag a
  `Seq.equal`
  serialize serialize_u8 (synth_asn1_tag_inverse a))

/// Specialied
///
val filter_the_asn1_tag
  (a: asn1_type)
  (b: byte)
: Ghost bool
  (requires True)
  (ensures fun r -> (r <==> filter_asn1_tag b /\ synth_asn1_tag b == a))

val synth_the_asn1_tag
  (a: asn1_type)
  (b: parse_filter_refine (filter_the_asn1_tag a))
: Ghost (the_asn1_type a)
  (requires True)
  (ensures fun a' -> (a' == synth_asn1_tag b))

val synth_the_asn1_tag_inverse
  (a: asn1_type)
  (a': the_asn1_type a)
: Ghost (parse_filter_refine (filter_the_asn1_tag a))
  (requires True)
  (ensures fun b -> (b == synth_asn1_tag_inverse a'))

val parse_the_asn1_tag
  (a: asn1_type)
: parser parse_asn1_tag_kind (the_asn1_type a)

val parse_the_asn1_tag_unfold
  (a: asn1_type)
  (input: bytes)
: Lemma (
  parse (parse_the_asn1_tag a) input ==
 (match parse parse_u8 input with
  | Some (x, consumed) -> if filter_the_asn1_tag a x then
                          ( Some (synth_the_asn1_tag a x, consumed) )
                          else
                          ( None )
  | None -> None))

val serialize_the_asn1_tag
  (a: asn1_type)
: serializer (parse_the_asn1_tag a)

val serialize_the_asn1_tag_unfold
  (a: asn1_type)
  (a': the_asn1_type a)
: Lemma (
  serialize (serialize_the_asn1_tag a) a'
  `Seq.equal`
  serialize serialize_u8 (synth_the_asn1_tag_inverse a a'))
