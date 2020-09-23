module ASN1.Spec.Value.BOOLEAN

open ASN1.Spec.Base
open LowParse.Spec.Int

open ASN1.Base

(* NOTE: Read after `ASN1.Spec.Tag`, `ASN1.Spec.Length` *)

(* NOTE: This module defines:
         1) The ASN1 `BOOLEAN` Value Parser and Serializer
         2) The ASN1 `BOOLEAN` TLV Parser and Serializer

         And each part is organized as:
         1) Aux (ghost) functions with prefix `filter_` to filter out invalid input bytes
         2) Aux (ghost) functions with prefix `synth_` to decode the valid input bytes into our
            representation of BOOLEAN values. These functions are injective.
         3) Aux (ghost) functions with prefix `synth_` and suffix `_inverse` to encode our
            representation of BOOLEAN into bytes. These functions are the inverse of
            corresponding synth functions.
         4) Functions with the prefix `parse_` are parsers constructed using parser combinators and
            aux functions.
         5) Functions with the prefix `serialize_` are serializers constructed using serializer
            combinators and aux functions.
         6) Lemma with suffix `_unfold` reveals the computation of parser/serialzier.
         7) Lemma with suffix `_size` reveals the length of a serialization.
*)

(* BOOLEAN primitive *)
/// filter valid input bytes
let filter_asn1_boolean b
= b = 0xFFuy || b = 0x00uy

/// decode input bytes
let synth_asn1_boolean b
= match b with
  | 0xFFuy -> true
  | 0x00uy -> false

/// encode input bytes
let synth_asn1_boolean_inverse b
= match b with
  | true  -> 0xFFuy
  | false -> 0x00uy

let parse_asn1_boolean
= parse_u8
  `parse_filter`
  filter_asn1_boolean
  `parse_synth`
  synth_asn1_boolean

let lemma_parse_asn1_boolean_unfold input
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

let serialize_asn1_boolean
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

let lemma_serialize_asn1_boolean_unfold b
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

let lemma_serialize_asn1_boolean_size b
= parser_kind_prop_equiv parse_asn1_boolean_kind parse_asn1_boolean;
  lemma_serialize_asn1_boolean_unfold b


/// Specialized TLV
///

open ASN1.Spec.Tag
open ASN1.Spec.Length

let synth_asn1_boolean_TLV a
= snd a

let synth_asn1_boolean_TLV_inverse x
= ((BOOLEAN, 1ul), x)

let parse_asn1_boolean_TLV
= parse_asn1_tag_of_type BOOLEAN
  `nondep_then`
  parse_asn1_length_of_type BOOLEAN
  `nondep_then`
  parse_asn1_boolean
  `parse_synth`
  synth_asn1_boolean_TLV

#push-options "--z3rlimit 16 --initial_ifuel 4"
let lemma_parse_asn1_boolean_TLV_unfold input_TLV
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

let serialize_asn1_boolean_TLV
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
let lemma_serialize_asn1_boolean_TLV_unfold value
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
let lemma_serialize_asn1_boolean_TLV_size value
= parser_kind_prop_equiv parse_asn1_boolean_TLV_kind parse_asn1_boolean_TLV;
  lemma_serialize_asn1_boolean_TLV_unfold value

let filter_asn1_boolean_true x
= x = true

let asn1_boolean_true = true

let parse_asn1_boolean_TLV_true
= parse_asn1_boolean_TLV
  `parse_filter`
  filter_asn1_boolean_true

let serialize_asn1_boolean_TLV_true
= serialize_asn1_boolean_TLV
  `serialize_filter`
  filter_asn1_boolean_true

let filter_asn1_boolean_false x
= x = false

let asn1_boolean_false = false

let parse_asn1_boolean_TLV_false
= parse_asn1_boolean_TLV
  `parse_filter`
  filter_asn1_boolean_false

let serialize_asn1_boolean_TLV_false
= serialize_asn1_boolean_TLV
  `serialize_filter`
  filter_asn1_boolean_false
