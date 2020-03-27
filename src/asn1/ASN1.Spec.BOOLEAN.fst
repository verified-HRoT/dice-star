module ASN1.Spec.BOOLEAN

include LowParse.Spec.Base
include LowParse.Spec.Combinators
include LowParse.Spec.Int

include ASN1.Base

(* BOOLEAN primitive *)
let filter_asn1_boolean
  (b: byte)
: GTot bool
= b = 0xFFuy || b = 0x00uy

let synth_asn1_boolean
  (b: parse_filter_refine filter_asn1_boolean)
: GTot bool
= match b with
  | 0xFFuy -> true
  | 0x00uy -> false

let synth_asn1_boolean_inverse
  (b: bool)
: GTot (r: parse_filter_refine filter_asn1_boolean{synth_asn1_boolean r == b})
= match b with
  | true  -> 0xFFuy
  | false -> 0x00uy

let parse_asn1_boolean
: parser parse_asn1_boolean_kind bool
= parse_u8
  `parse_filter`
  filter_asn1_boolean
  `parse_synth`
  synth_asn1_boolean

let parse_asn1_boolean_unfold
  (input: bytes)
: Lemma (
  parse parse_asn1_boolean input ==
 (match parse parse_u8 input with
  | Some (x, consumed) -> if filter_asn1_boolean x then
                          ( Some (synth_asn1_boolean x, consumed) )
                          else
                          ( None )
  | None -> None))
= parser_kind_prop_equiv parse_asn1_boolean_kind parse_asn1_boolean;
  parse_filter_eq
  (* p  *) (parse_u8)
  (* f  *) (filter_asn1_boolean)
  (* in *) (input);
  parse_synth_eq
  (* p1 *) (parse_u8
            `parse_filter`
            filter_asn1_boolean)
  (* f2 *) (synth_asn1_boolean)
  (* in *) (input)

let serialize_asn1_boolean
: serializer parse_asn1_boolean
= serialize_synth
  (* p1 *) (parse_u8
            `parse_filter`
            filter_asn1_boolean)
  (* f2 *) (synth_asn1_boolean)
  (* s1 *) (serialize_u8
            `serialize_filter`
            filter_asn1_boolean)
  (* g1 *) (synth_asn1_boolean_inverse)
  (* prf*) ()

let serialize_asn1_boolean_unfold
  (b: bool)
: Lemma (
  serialize serialize_asn1_boolean b
  `Seq.equal`
  serialize serialize_u8 (synth_asn1_boolean_inverse b))
= serialize_synth_eq
  (* p1 *) (parse_u8
            `parse_filter`
            filter_asn1_boolean)
  (* f2 *) (synth_asn1_boolean)
  (* s1 *) (serialize_u8
            `serialize_filter`
            filter_asn1_boolean)
  (* g1 *) (synth_asn1_boolean_inverse)
  (* prf*) ()
  (* in *) (b)
