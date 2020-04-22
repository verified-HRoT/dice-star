module ASN1.Spec.BOOLEAN

open LowParse.Spec.Base
open LowParse.Spec.Combinators
open LowParse.Spec.Int

open ASN1.Base

(* BOOLEAN primitive *)
/// filter valid input bytes
noextract
let filter_asn1_boolean
  (b: byte)
: GTot bool
= b = 0xFFuy || b = 0x00uy

/// decode input bytes
noextract
let synth_asn1_boolean
  (b: parse_filter_refine filter_asn1_boolean)
: GTot (datatype_of_asn1_type BOOLEAN)
= match b with
  | 0xFFuy -> true
  | 0x00uy -> false

/// encode input bytes
noextract
let synth_asn1_boolean_inverse
  (b: datatype_of_asn1_type BOOLEAN)
: GTot (r: parse_filter_refine filter_asn1_boolean{synth_asn1_boolean r == b})
= match b with
  | true  -> 0xFFuy
  | false -> 0x00uy

noextract
let parse_asn1_boolean_kind = strong_parser_kind 1 1 None

noextract
let parse_asn1_boolean
: parser parse_asn1_boolean_kind (datatype_of_asn1_type BOOLEAN)
= parse_u8
  `parse_filter`
  filter_asn1_boolean
  `parse_synth`
  synth_asn1_boolean

noextract
let parse_asn1_boolean_unfold
  (input: bytes)
: Lemma (
  parse parse_asn1_boolean input ==
 (match parse parse_u8 input with
  | Some (x, consumed) -> if filter_asn1_boolean x then
                          ( Some (synth_asn1_boolean x, consumed) )
                          else
                          ( None )
  | None -> None) /\
 (Some? (parse parse_asn1_boolean input) ==>
   Seq.length input > 0 /\
   parse parse_u8 input == Some (input.[0], 1)))
= parser_kind_prop_equiv parse_asn1_boolean_kind parse_asn1_boolean;
  parser_kind_prop_equiv parse_u8_kind parse_u8;
  if Seq.length input > 0 then
  ( parse_u8_spec  input
  ; parse_u8_spec' input );
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

noextract
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

noextract
let serialize_asn1_boolean_unfold
  (b: datatype_of_asn1_type BOOLEAN)
: Lemma (
  serialize serialize_u8 (synth_asn1_boolean_inverse b)
  `Seq.equal`
  Seq.create 1 (synth_asn1_boolean_inverse b) /\
  serialize serialize_asn1_boolean b
  `Seq.equal`
  serialize serialize_u8 (synth_asn1_boolean_inverse b))
= serialize_u8_spec  (synth_asn1_boolean_inverse b);
  serialize_u8_spec' (synth_asn1_boolean_inverse b);
  serialize_synth_eq
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

noextract
let serialize_asn1_boolean_size
  (b: datatype_of_asn1_type BOOLEAN)
: Lemma (
  Seq.length (serialize serialize_asn1_boolean b) == 1)
= parser_kind_prop_equiv parse_asn1_boolean_kind parse_asn1_boolean;
  serialize_asn1_boolean_unfold b


/// Specialized TLV
///

open ASN1.Spec.Tag
open ASN1.Spec.Length

noextract
let synth_asn1_boolean_TLV
  (a: (the_asn1_type BOOLEAN * asn1_int32_of_type BOOLEAN) * datatype_of_asn1_type BOOLEAN)
: GTot (datatype_of_asn1_type BOOLEAN)
= snd a

noextract
let synth_asn1_boolean_TLV_inverse
  (x: datatype_of_asn1_type BOOLEAN)
: GTot (a: ((the_asn1_type BOOLEAN * asn1_int32_of_type BOOLEAN) * datatype_of_asn1_type BOOLEAN){x == synth_asn1_boolean_TLV a})
= ((BOOLEAN, 1ul), x)

noextract
let parse_asn1_boolean_TLV_kind
: parser_kind
= strong_parser_kind 3 3 None

noextract
let parse_asn1_boolean_TLV
: parser parse_asn1_boolean_TLV_kind (datatype_of_asn1_type BOOLEAN)
= parse_asn1_tag_of_type BOOLEAN
  `nondep_then`
  parse_asn1_length_of_type BOOLEAN
  `nondep_then`
  parse_asn1_boolean
  `parse_synth`
  synth_asn1_boolean_TLV

#push-options "--query_stats --z3rlimit 16 --initial_ifuel 4"
noextract
let parse_asn1_boolean_TLV_unfold
  (input_TLV: bytes)
: Lemma (
  parse parse_asn1_boolean_TLV input_TLV ==
 (parser_kind_prop_equiv parse_asn1_tag_kind (parse_asn1_tag_of_type BOOLEAN);
  match parse (parse_asn1_tag_of_type BOOLEAN) input_TLV with
  | None -> None
  | Some (BOOLEAN, 1) ->
    (parser_kind_prop_equiv (parse_asn1_length_kind_of_type BOOLEAN) (parse_asn1_length_of_type BOOLEAN);
     let input_LV = Seq.slice input_TLV 1 (Seq.length input_TLV) in
     match parse (parse_asn1_length_of_type BOOLEAN) input_LV with
     | None -> None
     | Some (1ul, 1) ->
       (parser_kind_prop_equiv parse_asn1_boolean_kind parse_asn1_boolean;
        let input_V = Seq.slice input_LV 1 (Seq.length input_LV) in
        match parse parse_asn1_boolean input_V with
        | None -> None
        | Some (value, 1) -> Some (value, (1 + 1 + 1 <: consumed_length input_TLV)))))
)
= parser_kind_prop_equiv parse_asn1_tag_kind (parse_asn1_tag_of_type BOOLEAN);
  parser_kind_prop_equiv (parse_asn1_length_kind_of_type BOOLEAN) (parse_asn1_length_of_type BOOLEAN);
  parser_kind_prop_equiv parse_asn1_boolean_kind parse_asn1_boolean;
  nondep_then_eq
  (* p1 *) (parse_asn1_tag_of_type BOOLEAN)
  (* p2 *) (parse_asn1_length_of_type BOOLEAN)
  (* in *) (input_TLV);
  nondep_then_eq
  (* p1 *) (parse_asn1_tag_of_type BOOLEAN
            `nondep_then`
            parse_asn1_length_of_type BOOLEAN)
  (* p2 *) (parse_asn1_boolean)
  (* in *) (input_TLV);
  parse_synth_eq
  (* p1 *) (parse_asn1_tag_of_type BOOLEAN
            `nondep_then`
            parse_asn1_length_of_type BOOLEAN
            `nondep_then`
            parse_asn1_boolean)
  (* f2 *) (synth_asn1_boolean_TLV)
  (* in *) (input_TLV)

noextract
let serialize_asn1_boolean_TLV
: serializer parse_asn1_boolean_TLV
= serialize_synth
  (* p1 *) (parse_asn1_tag_of_type BOOLEAN
            `nondep_then`
            parse_asn1_length_of_type BOOLEAN
            `nondep_then`
            parse_asn1_boolean)
  (* f2 *) (synth_asn1_boolean_TLV)
  (* s1 *) (serialize_asn1_tag_of_type BOOLEAN
            `serialize_nondep_then`
            serialize_asn1_length_of_type BOOLEAN
            `serialize_nondep_then`
            serialize_asn1_boolean)
  (* g1 *) (synth_asn1_boolean_TLV_inverse)
  (* Prf*) ()

(* NOTE: How far should we unfold the computation? *)
noextract
let serialize_asn1_boolean_TLV_unfold
  (value: datatype_of_asn1_type BOOLEAN)
: Lemma (
  serialize serialize_asn1_boolean_TLV value
  `Seq.equal`
 (serialize (serialize_asn1_tag_of_type BOOLEAN) BOOLEAN
  `Seq.append`
  serialize (serialize_asn1_length_of_type BOOLEAN) 1ul
  `Seq.append`
  serialize serialize_asn1_boolean value)
)
= serialize_nondep_then_eq
  (* s1 *) (serialize_asn1_tag_of_type BOOLEAN)
  (* s2 *) (serialize_asn1_length_of_type BOOLEAN)
  (* in *) (BOOLEAN, 1ul);
  serialize_nondep_then_eq
  (* s1 *) (serialize_asn1_tag_of_type BOOLEAN
            `serialize_nondep_then`
            serialize_asn1_length_of_type BOOLEAN)
  (* s2 *) (serialize_asn1_boolean)
  (* in *) ((BOOLEAN, 1ul), value);
  serialize_synth_eq
  (* p1 *) (parse_asn1_tag_of_type BOOLEAN
            `nondep_then`
            parse_asn1_length_of_type BOOLEAN
            `nondep_then`
            parse_asn1_boolean)
  (* f2 *) (synth_asn1_boolean_TLV)
  (* s1 *) (serialize_asn1_tag_of_type BOOLEAN
            `serialize_nondep_then`
            serialize_asn1_length_of_type BOOLEAN
            `serialize_nondep_then`
            serialize_asn1_boolean)
  (* g1 *) (synth_asn1_boolean_TLV_inverse)
  (* Prf*) ()
  (* in *) (value)

(* NOTE: Should we just combine this lemma into `_unfold` lemmas? *)
noextract
let serialize_asn1_boolean_TLV_size
  (value: datatype_of_asn1_type BOOLEAN)
: Lemma (
  Seq.length (serialize serialize_asn1_boolean_TLV value) == 3)
= parser_kind_prop_equiv parse_asn1_boolean_TLV_kind parse_asn1_boolean_TLV;
  serialize_asn1_boolean_TLV_unfold value
