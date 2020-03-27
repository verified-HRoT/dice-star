module ASN1.Spec.Tag

open LowParse.Spec.Base
open LowParse.Spec.Combinators
open LowParse.Spec.Int

open ASN1.Base

(* Tag parser primitive *)

let filter_asn1_tag
  (b: byte)
: Ghost bool
  (requires True)
  (ensures fun r -> r == (b = 0x01uy || b = 0x04uy || b = 0x05uy))
= match b with
  | 0x01uy | 0x04uy | 0x05uy -> true
  | _ -> false

let synth_asn1_tag
  (b: parse_filter_refine filter_asn1_tag)
: Ghost asn1_type
  (requires True)
  (ensures fun a ->
    a == (match b with
          | 0x01uy -> BOOLEAN
          | 0x04uy -> OCTET_STRING
          | 0x05uy -> NULL))
= match b with
  | 0x01uy -> BOOLEAN
  | 0x04uy -> OCTET_STRING
  | 0x05uy -> NULL

let synth_asn1_tag_inverse
  (a: asn1_type)
: Ghost (b: parse_filter_refine filter_asn1_tag{a == synth_asn1_tag b})
  (requires True)
  (ensures fun b -> a == synth_asn1_tag b)
= match a with
  | BOOLEAN      -> 0x01uy
  // | INTEGER      -> 0x02uy
  // | BIT_STRING   -> 0x03uy
  | OCTET_STRING -> 0x04uy
  | NULL         -> 0x05uy
  // | OID          -> 0x06uy
  // | SEQUENCE     -> 0x30uy

let parse_asn1_tag
: parser parse_asn1_tag_kind asn1_type
= parse_u8
  `parse_filter`
  filter_asn1_tag
  `parse_synth`
  synth_asn1_tag

let parse_asn1_tag_unfold
  (input: bytes)
: Lemma (
  parse parse_asn1_tag input ==
 (match parse parse_u8 input with
  | Some (x, consumed) -> if filter_asn1_tag x then
                          ( Some (synth_asn1_tag x, consumed) )
                          else
                          ( None )
  | None -> None))
= parser_kind_prop_equiv parse_asn1_tag_kind parse_asn1_tag;
  parse_filter_eq
  (* p  *) (parse_u8)
  (* f  *) (filter_asn1_tag)
  (* in *) (input);
  parse_synth_eq
  (* p1 *) (parse_u8
            `parse_filter`
            filter_asn1_tag)
  (* f2 *) (synth_asn1_tag)
  (* in *) (input)

let serialize_asn1_tag
: serializer parse_asn1_tag
= serialize_synth
  (* p1 *) (parse_u8
            `parse_filter`
            filter_asn1_tag)
  (* f2 *) (synth_asn1_tag)
  (* s1 *) (serialize_u8
            `serialize_filter`
            filter_asn1_tag)
  (* g1 *) (synth_asn1_tag_inverse)
  (* prf*) ()

let serialize_asn1_tag_unfold
  (a: asn1_type)
: Lemma (
  serialize serialize_asn1_tag a
  `Seq.equal`
  serialize serialize_u8 (synth_asn1_tag_inverse a))
= serialize_synth_eq
  (* p1 *) (parse_u8
            `parse_filter`
            filter_asn1_tag)
  (* f2 *) (synth_asn1_tag)
  (* s1 *) (serialize_u8
            `serialize_filter`
            filter_asn1_tag)
  (* g1 *) (synth_asn1_tag_inverse)
  (* prf*) ()
  (* in *) (a)
