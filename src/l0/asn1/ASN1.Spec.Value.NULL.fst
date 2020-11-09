module ASN1.Spec.Value.NULL

open ASN1.Spec.Base

open ASN1.Base
open ASN1.Spec.Tag
open ASN1.Spec.Length

(* NOTE: Read after `ASN1.Spec.Tag`, `ASN1.Spec.Length` *)
(* NOTE: This module defines:
         1) The ASN1 `ASN1_NULL` Value Parser and Serializer
         2) The ASN1 `ASN1_NULL` TLV Parser and Serializer
*)

///////////////////////////////////////////////////////////////
////  ASN1 `ASN1_NULL` Value Parser/Serializer
///////////////////////////////////////////////////////////////

///
/// ASN1 `ASN1_NULL` value parser parses nothing and returns `()`
/// using the `parse_ret` combinator
///
let parse_asn1_ASN1_NULL
= parse_ret
  (* v *) ()

///
/// ASN1 `ASN1_NULL` value parser serialize `()` to empty bytes
/// using the `serialize_ret` combinator
///
let serialize_asn1_ASN1_NULL
= serialize_ret
  (* v *) ()
  (*prf*) (fun n -> ())

///
/// Lemmas
///

/// Reveal the computation of serialize
let lemma_serialize_asn1_ASN1_NULL_unfold value
= ()

/// Reveal the size of a serialiaztion
let lemma_serialize_asn1_ASN1_NULL_size value
= parser_kind_prop_equiv parse_asn1_ASN1_NULL_kind parse_asn1_ASN1_NULL;
  lemma_serialize_asn1_ASN1_NULL_unfold value

///////////////////////////////////////////////////////////////
////  ASN1 `ASN1_NULL` TLV Parser/Serializer
///////////////////////////////////////////////////////////////

/// Synthesize the TLV of a `ASN1_NULL` value
let synth_asn1_ASN1_NULL_TLV a
= snd a

/// Synthesize th `ASN1_NULL` value from a `ASN1_NULL` TLV
noextract
let synth_asn1_ASN1_NULL_TLV_inverse x
= ((ASN1_NULL, 0ul), x)


///
/// `ASN1_NULL` TLV parser
///
let parse_asn1_ASN1_NULL_TLV
= parse_asn1_tag_of_type ASN1_NULL
  `nondep_then`
  parse_asn1_length_of_type ASN1_NULL
  `nondep_then`
  parse_asn1_ASN1_NULL
  `parse_synth`
  synth_asn1_ASN1_NULL_TLV

///
/// `ASN1_NULL` TLV serialzier
///
let serialize_asn1_ASN1_NULL_TLV
= serialize_synth
  (* p1 *) (parse_asn1_tag_of_type ASN1_NULL
            `nondep_then`
            parse_asn1_length_of_type ASN1_NULL
            `nondep_then`
            parse_asn1_ASN1_NULL)
  (* f2 *) (synth_asn1_ASN1_NULL_TLV)
  (* s1 *) (serialize_asn1_tag_of_type ASN1_NULL
            `serialize_nondep_then`
            serialize_asn1_length_of_type ASN1_NULL
            `serialize_nondep_then`
            serialize_asn1_ASN1_NULL)
  (* g1 *) (synth_asn1_ASN1_NULL_TLV_inverse)
  (* Prf*) ()

///
/// Lemmas
///

/// Reveal the computation of parse
let lemma_parse_asn1_ASN1_NULL_TLV_unfold input_TLV
= nondep_then_eq
  (* p1 *) (parse_asn1_tag_of_type ASN1_NULL)
  (* p2 *) (parse_asn1_length_of_type ASN1_NULL)
  (* in *) (input_TLV);
  nondep_then_eq
  (* p1 *) (parse_asn1_tag_of_type ASN1_NULL
            `nondep_then`
            parse_asn1_length_of_type ASN1_NULL)
  (* p2 *) (parse_asn1_ASN1_NULL)
  (* in *) (input_TLV);
  parse_synth_eq
  (* p1 *) (parse_asn1_tag_of_type ASN1_NULL
            `nondep_then`
            parse_asn1_length_of_type ASN1_NULL
            `nondep_then`
            parse_asn1_ASN1_NULL)
  (* f2 *) (synth_asn1_ASN1_NULL_TLV)
  (* in *) (input_TLV)

/// Reveal the computation of serialize
let lemma_serialize_asn1_ASN1_NULL_TLV_unfold value
= serialize_nondep_then_eq
  (* s1 *) (serialize_asn1_tag_of_type ASN1_NULL)
  (* s2 *) (serialize_asn1_length_of_type ASN1_NULL)
  (* in *) (ASN1_NULL, 0ul);
  serialize_nondep_then_eq
  (* s1 *) (serialize_asn1_tag_of_type ASN1_NULL
            `serialize_nondep_then`
            serialize_asn1_length_of_type ASN1_NULL)
  (* s2 *) (serialize_asn1_ASN1_NULL)
  (* in *) ((ASN1_NULL, 0ul), value);
  serialize_synth_eq
  (* p1 *) (parse_asn1_tag_of_type ASN1_NULL
            `nondep_then`
            parse_asn1_length_of_type ASN1_NULL
            `nondep_then`
            parse_asn1_ASN1_NULL)
  (* f2 *) (synth_asn1_ASN1_NULL_TLV)
  (* s1 *) (serialize_asn1_tag_of_type ASN1_NULL
            `serialize_nondep_then`
            serialize_asn1_length_of_type ASN1_NULL
            `serialize_nondep_then`
            serialize_asn1_ASN1_NULL)
  (* g1 *) (synth_asn1_ASN1_NULL_TLV_inverse)
  (* Prf*) ()
  (* in *) (value)

/// Reveal the length of a serialization
let lemma_serialize_asn1_ASN1_NULL_TLV_size value
= lemma_serialize_asn1_ASN1_NULL_TLV_unfold value
