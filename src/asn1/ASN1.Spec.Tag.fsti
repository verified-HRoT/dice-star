module ASN1.Spec.Tag

include LowParse.Spec.Base
include LowParse.Spec.Combinators
include LowParse.Spec.Int

include ASN1.Base

val filter_asn1_tag
  (b: byte)
: Ghost bool
  (requires True)
  (ensures fun r -> r == (b = 0x01uy || b = 0x04uy || b = 0x05uy))

let valid_asn1_tag_byte = parse_filter_refine filter_asn1_tag

val synth_asn1_tag
  (b: parse_filter_refine filter_asn1_tag)
: Ghost asn1_type
  (requires True)
  (ensures fun a ->
    a == (match b with
          | 0x01uy -> BOOLEAN
          | 0x04uy -> OCTET_STRING
          | 0x05uy -> NULL))

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
