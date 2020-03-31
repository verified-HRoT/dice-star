module ASN1.Spec.BOOLEAN

open LowParse.Spec.Base
open LowParse.Spec.Combinators
open LowParse.Spec.Int

open ASN1.Base
open ASN1.Spec.Tag
open ASN1.Spec.Length

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

/// Specialized TLV
///
let synth_asn1_boolean_TLV
  (a: (the_asn1_type BOOLEAN * asn1_length_of_tag BOOLEAN) * datatype_of_asn1_type BOOLEAN)
: GTot (datatype_of_asn1_type BOOLEAN)
= snd a

let synth_asn1_boolean_TLV_inverse
  (x: datatype_of_asn1_type BOOLEAN)
: GTot (a: ((the_asn1_type BOOLEAN * asn1_length_of_tag BOOLEAN) * datatype_of_asn1_type BOOLEAN){x == synth_asn1_boolean_TLV a})
= ((BOOLEAN, len_of_asn1_data BOOLEAN x), x)

let parse_asn1_boolean_TLV
: parser _ (datatype_of_asn1_type BOOLEAN)
= parse_the_asn1_tag BOOLEAN
  `nondep_then`
  parse_asn1_length_of_tag BOOLEAN
  `nondep_then`
  parse_asn1_boolean
  `parse_synth`
  synth_asn1_boolean_TLV

let serialize_asn1_boolean_TLV
: serializer parse_asn1_boolean_TLV
= serialize_synth
  (* p1 *) (parse_the_asn1_tag BOOLEAN
            `nondep_then`
            parse_asn1_length_of_tag BOOLEAN
            `nondep_then`
            parse_asn1_boolean)
  (* f2 *) (synth_asn1_boolean_TLV)
  (* s1 *) (serialize_the_asn1_tag BOOLEAN
            `serialize_nondep_then`
            serialize_asn1_length_of_tag BOOLEAN
            `serialize_nondep_then`
            serialize_asn1_boolean)
  (* g1 *) (synth_asn1_boolean_TLV_inverse)
  (* Prf*) ()

(* TODO: interface and unfold spec *)
