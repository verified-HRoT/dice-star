module ASN1.Spec.NULL

open LowParse.Spec.Base
open LowParse.Spec.Combinators

open ASN1.Base
open ASN1.Spec.Tag
open ASN1.Spec.Length

noextract
let parse_asn1_null_kind = parse_ret_kind

noextract
let parse_asn1_null
: parser parse_asn1_null_kind (datatype_of_asn1_type NULL)
= parse_ret
  (* v *) ()

noextract
let serialize_asn1_null
: serializer parse_asn1_null
= serialize_ret
  (* v *) ()
  (*prf*) (fun n -> ())

noextract
let serialize_asn1_null_unfold
  (value: datatype_of_asn1_type NULL)
: Lemma (
  serialize serialize_asn1_null value == Seq.empty)
= ()

noextract
let serialize_asn1_null_size
  (value: datatype_of_asn1_type NULL)
: Lemma (
  Seq.length (serialize serialize_asn1_null value) == 0)
= parser_kind_prop_equiv parse_asn1_null_kind parse_asn1_null;
  serialize_asn1_null_unfold value

/// Specialized TLV
///
noextract
let synth_asn1_null_TLV
  (a: (the_asn1_type NULL * asn1_value_int32_of_type NULL) * datatype_of_asn1_type NULL)
: GTot (datatype_of_asn1_type NULL)
= snd a

noextract
let synth_asn1_null_TLV_inverse
  (x: datatype_of_asn1_type NULL)
: GTot (a: ((the_asn1_type NULL * asn1_value_int32_of_type NULL) * datatype_of_asn1_type NULL){x == synth_asn1_null_TLV a})
= ((NULL, 0ul), x)

noextract
let parse_asn1_null_TLV_kind
: parser_kind
= strong_parser_kind 2 2 None

noextract
let parse_asn1_null_TLV
: parser parse_asn1_null_TLV_kind (datatype_of_asn1_type NULL)
= parse_asn1_tag_of_type NULL
  `nondep_then`
  parse_asn1_length_of_type NULL
  `nondep_then`
  parse_asn1_null
  `parse_synth`
  synth_asn1_null_TLV

noextract
let serialize_asn1_null_TLV
: serializer parse_asn1_null_TLV
= serialize_synth
  (* p1 *) (parse_asn1_tag_of_type NULL
            `nondep_then`
            parse_asn1_length_of_type NULL
            `nondep_then`
            parse_asn1_null)
  (* f2 *) (synth_asn1_null_TLV)
  (* s1 *) (serialize_asn1_tag_of_type NULL
            `serialize_nondep_then`
            serialize_asn1_length_of_type NULL
            `serialize_nondep_then`
            serialize_asn1_null)
  (* g1 *) (synth_asn1_null_TLV_inverse)
  (* Prf*) ()

noextract
let parse_asn1_null_TLV_unfold
  (input_TLV: bytes)
: Lemma (
  parse parse_asn1_null_TLV input_TLV ==
 (match parse (parse_asn1_tag_of_type NULL) input_TLV with
  | None -> None
  | Some (NULL, consumed_T) ->
    (let input_LV = Seq.slice input_TLV consumed_T (Seq.length input_TLV) in
     match parse (parse_asn1_length_of_type NULL) input_LV with
     | None -> None
     | Some (0ul, consumed_L) ->
       (let input_V = Seq.slice input_LV consumed_L (Seq.length input_LV) in
        match parse parse_asn1_null input_V with
        | None -> None
        | Some (value, consumed_V) -> Some (value, (consumed_T + consumed_L + consumed_V <: consumed_length input_TLV)))))
)
= nondep_then_eq
  (* p1 *) (parse_asn1_tag_of_type NULL)
  (* p2 *) (parse_asn1_length_of_type NULL)
  (* in *) (input_TLV);
  nondep_then_eq
  (* p1 *) (parse_asn1_tag_of_type NULL
            `nondep_then`
            parse_asn1_length_of_type NULL)
  (* p2 *) (parse_asn1_null)
  (* in *) (input_TLV);
  parse_synth_eq
  (* p1 *) (parse_asn1_tag_of_type NULL
            `nondep_then`
            parse_asn1_length_of_type NULL
            `nondep_then`
            parse_asn1_null)
  (* f2 *) (synth_asn1_null_TLV)
  (* in *) (input_TLV)

noextract
let serialize_asn1_null_TLV_unfold
  (value: datatype_of_asn1_type NULL)
: Lemma (
  serialize serialize_asn1_null_TLV value
  `Seq.equal`
 (serialize (serialize_asn1_tag_of_type NULL) NULL
  `Seq.append`
  serialize (serialize_asn1_length_of_type NULL) 0ul
  `Seq.append`
  serialize serialize_asn1_null value)
)
= serialize_nondep_then_eq
  (* s1 *) (serialize_asn1_tag_of_type NULL)
  (* s2 *) (serialize_asn1_length_of_type NULL)
  (* in *) (NULL, 0ul);
  serialize_nondep_then_eq
  (* s1 *) (serialize_asn1_tag_of_type NULL
            `serialize_nondep_then`
            serialize_asn1_length_of_type NULL)
  (* s2 *) (serialize_asn1_null)
  (* in *) ((NULL, 0ul), value);
  serialize_synth_eq
  (* p1 *) (parse_asn1_tag_of_type NULL
            `nondep_then`
            parse_asn1_length_of_type NULL
            `nondep_then`
            parse_asn1_null)
  (* f2 *) (synth_asn1_null_TLV)
  (* s1 *) (serialize_asn1_tag_of_type NULL
            `serialize_nondep_then`
            serialize_asn1_length_of_type NULL
            `serialize_nondep_then`
            serialize_asn1_null)
  (* g1 *) (synth_asn1_null_TLV_inverse)
  (* Prf*) ()
  (* in *) (value)

noextract
let serialize_asn1_null_TLV_size
  (value: datatype_of_asn1_type NULL)
: Lemma (
  Seq.length (serialize serialize_asn1_null_TLV value) == 2)
= serialize_asn1_null_TLV_unfold value
