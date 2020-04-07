module ASN1.Spec.NULL

open LowParse.Spec.Base
open LowParse.Spec.Combinators

open ASN1.Base
open ASN1.Spec.Tag
open ASN1.Spec.Length

let parse_asn1_null_kind = parse_ret_kind
let parse_asn1_null
: parser parse_asn1_null_kind (datatype_of_asn1_type NULL)
= parse_ret
  (* v *) ()

let serialize_asn1_null
: serializer parse_asn1_null
= serialize_ret
  (* v *) ()
  (*prf*) (fun n -> ())

/// Specialized TLV
///
let synth_asn1_null_TLV
  (a: (the_asn1_type NULL * asn1_int32_of_type NULL) * datatype_of_asn1_type NULL)
: GTot (datatype_of_asn1_type NULL)
= snd a

let synth_asn1_null_TLV_inverse
  (x: datatype_of_asn1_type NULL)
: GTot (a: ((the_asn1_type NULL * asn1_int32_of_type NULL) * datatype_of_asn1_type NULL){x == synth_asn1_null_TLV a})
= ((NULL, len_of_asn1_data NULL x), x)

let parse_asn1_null_TLV_kind
: parser_kind
= parse_asn1_tag_kind
  `and_then_kind`
  parse_asn1_length_kind_of_type NULL
  `and_then_kind`
  parse_asn1_null_kind

let parse_asn1_null_TLV
: parser _ (datatype_of_asn1_type NULL)
= parse_the_asn1_tag NULL
  `nondep_then`
  parse_asn1_length_of_type NULL
  `nondep_then`
  parse_asn1_null
  `parse_synth`
  synth_asn1_null_TLV

let serialize_asn1_null_TLV
: serializer parse_asn1_null_TLV
= serialize_synth
  (* p1 *) (parse_the_asn1_tag NULL
            `nondep_then`
            parse_asn1_length_of_type NULL
            `nondep_then`
            parse_asn1_null)
  (* f2 *) (synth_asn1_null_TLV)
  (* s1 *) (serialize_the_asn1_tag NULL
            `serialize_nondep_then`
            serialize_asn1_length_of_type NULL
            `serialize_nondep_then`
            serialize_asn1_null)
  (* g1 *) (synth_asn1_null_TLV_inverse)
  (* Prf*) ()

let parse_asn1_null_TLV_unfold
  (input_TLV: bytes)
: Lemma (
  parse parse_asn1_null_TLV input_TLV ==
 (match parse (parse_the_asn1_tag NULL) input_TLV with
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
  (* p1 *) (parse_the_asn1_tag NULL)
  (* p2 *) (parse_asn1_length_of_type NULL)
  (* in *) (input_TLV);
  nondep_then_eq
  (* p1 *) (parse_the_asn1_tag NULL
            `nondep_then`
            parse_asn1_length_of_type NULL)
  (* p2 *) (parse_asn1_null)
  (* in *) (input_TLV);
  parse_synth_eq
  (* p1 *) (parse_the_asn1_tag NULL
            `nondep_then`
            parse_asn1_length_of_type NULL
            `nondep_then`
            parse_asn1_null)
  (* f2 *) (synth_asn1_null_TLV)
  (* in *) (input_TLV)

let serialize_asn1_null_TLV_unfold
  (value: datatype_of_asn1_type NULL)
: Lemma (
  serialize serialize_asn1_null_TLV value
  `Seq.equal`
 (serialize (serialize_the_asn1_tag NULL) NULL
  `Seq.append`
  serialize (serialize_asn1_length_of_type NULL) 0ul
  `Seq.append`
  serialize serialize_asn1_null value)
)
= serialize_nondep_then_eq
  (* s1 *) (serialize_the_asn1_tag NULL)
  (* s2 *) (serialize_asn1_length_of_type NULL)
  (* in *) (NULL, 0ul);
  serialize_nondep_then_eq
  (* s1 *) (serialize_the_asn1_tag NULL
            `serialize_nondep_then`
            serialize_asn1_length_of_type NULL)
  (* s2 *) (serialize_asn1_null)
  (* in *) ((NULL, 0ul), value);
  serialize_synth_eq
  (* p1 *) (parse_the_asn1_tag NULL
            `nondep_then`
            parse_asn1_length_of_type NULL
            `nondep_then`
            parse_asn1_null)
  (* f2 *) (synth_asn1_null_TLV)
  (* s1 *) (serialize_the_asn1_tag NULL
            `serialize_nondep_then`
            serialize_asn1_length_of_type NULL
            `serialize_nondep_then`
            serialize_asn1_null)
  (* g1 *) (synth_asn1_null_TLV_inverse)
  (* Prf*) ()
  (* in *) (value)
