module ASN1.Spec.BOOLEAN

open LowParse.Spec.Base
open LowParse.Spec.Combinators
open LowParse.Spec.Int

open ASN1.Base

(* BOOLEAN primitive *)
val filter_asn1_boolean
  (b: byte)
: Ghost bool
  (requires True)
  (ensures fun r -> r == (b = 0xFFuy || b = 0x00uy))

let valid_asn1_boolean_byte = parse_filter_refine filter_asn1_boolean

val synth_asn1_boolean
    (b: parse_filter_refine filter_asn1_boolean)
: Ghost bool
  (requires True)
  (ensures fun x -> x == (b = 0xFFuy))

val synth_asn1_boolean_inverse
  (x: bool)
: Ghost (b: parse_filter_refine filter_asn1_boolean{synth_asn1_boolean b == x})
  (requires True)
  (ensures fun b -> synth_asn1_boolean b == x)

let parse_asn1_boolean_kind = strong_parser_kind 1 1 None
val parse_asn1_boolean
: parser parse_asn1_boolean_kind bool

val parse_asn1_boolean_unfold
  (input: bytes)
: Lemma (
  parser_kind_prop parse_asn1_boolean_kind parse_asn1_boolean /\
  parse parse_asn1_boolean input ==
 (match parse parse_u8 input with
  | Some (x, consumed) -> if filter_asn1_boolean x then
                          ( Some (synth_asn1_boolean x, consumed) )
                          else
                          ( None )
  | None -> None))

val serialize_asn1_boolean
: serializer parse_asn1_boolean

val serialize_asn1_boolean_unfold
  (b: bool)
: Lemma (
  serialize serialize_asn1_boolean b
  `Seq.equal`
  serialize serialize_u8 (synth_asn1_boolean_inverse b))

