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
  (a: (the_asn1_type NULL * asn1_int32_of_tag NULL) * datatype_of_asn1_type NULL)
: GTot (datatype_of_asn1_type NULL)
= snd a

let synth_asn1_null_TLV_inverse
  (x: datatype_of_asn1_type NULL)
: GTot (a: ((the_asn1_type NULL * asn1_int32_of_tag NULL) * datatype_of_asn1_type NULL){x == synth_asn1_null_TLV a})
= ((NULL, len_of_asn1_data NULL x), x)

let parse_asn1_null_TLV_kind
: parser_kind
= parse_asn1_tag_kind
  `and_then_kind`
  parse_asn1_length_kind_of_tag NULL
  `and_then_kind`
  parse_asn1_null_kind

let parse_asn1_null_TLV
: parser _ (datatype_of_asn1_type NULL)
= parse_the_asn1_tag NULL
  `nondep_then`
  parse_asn1_length_of_tag NULL
  `nondep_then`
  parse_asn1_null
  `parse_synth`
  synth_asn1_null_TLV

let serialize_asn1_null_TLV
: serializer parse_asn1_null_TLV
= serialize_synth
  (* p1 *) (parse_the_asn1_tag NULL
            `nondep_then`
            parse_asn1_length_of_tag NULL
            `nondep_then`
            parse_asn1_null)
  (* f2 *) (synth_asn1_null_TLV)
  (* s1 *) (serialize_the_asn1_tag NULL
            `serialize_nondep_then`
            serialize_asn1_length_of_tag NULL
            `serialize_nondep_then`
            serialize_asn1_null)
  (* g1 *) (synth_asn1_null_TLV_inverse)
  (* Prf*) ()
