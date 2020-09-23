module ASN1.Spec.Tag

open ASN1.Spec.Base
open LowParse.Spec.Int

open ASN1.Base

(* NOTE: This module defines:
         1) the _generic_ ASN1 Tag parser/serializer for _any_ ASN1 Tag
         2) the _specialized_ ASN1 Tag parser/serializer for a _given_ ASN1 Tag

         And each part is organized as:
         1) Aux (ghost) functions with prefix `filter_` to filter out invalid input bytes
         2) Aux (ghost) functions with prefix `synth_` to decode the valid input bytes/synthesize
            ASN1 tags. These functions are injective.
         3) Aux (ghost) functions with prefix `synth_` and suffix `_inverse` to encode ASN1 tags to
            bytes. These functions are the inverse of corresponding synth functions.
         4) Functions with the prefix `parse_` are parsers constructed using parser combinators and
            aux functions.
         5) Functions with the prefix `serialize_` are serializers constructed using serializer
            combinators and aux functions.
         6) Lemma with suffix `_unfold` reveals the computation of parser/serialzier.
         7) Lemma with suffix `_size` reveals the length of a serialization.
*)


/////////////////////////////////////////
////   Generic ASN1 Tag Parser
/////////////////////////////////////////
open FStar.Integers
/// filter valid input bytes

let filter_asn1_tag b =
  match b with
  | 0x01uy | 0x04uy | 0x05uy | 0x13uy | 0x16uy | 0x18uy | 0x30uy | 0x31uy | 0x03uy | 0x02uy | 0x06uy -> true
  | _ -> if (b / 0b01000000uy <> 00uy) then true else false

/// decode input bytes

#push-options "--z3rlimit 32"
let synth_asn1_tag b
= match b with
  | 0x01uy -> BOOLEAN
  | 0x02uy -> INTEGER
  | 0x03uy -> BIT_STRING
  | 0x04uy -> OCTET_STRING
  | 0x13uy -> PRINTABLE_STRING
  | 0x16uy -> IA5_STRING
  | 0x05uy -> ASN1_NULL
  | 0x06uy -> OID
  | 0x18uy -> Generalized_Time
  | 0x30uy -> SEQUENCE
  | 0x31uy -> SET
  | _      -> ( let tag_class = match b / 0b01000000uy <: byte with
                                | 0b01uy -> APPLICATION
                                | 0b10uy -> CONTEXT_SPECIFIC
                                | 0b11uy -> PRIVATE in
                let tag_form  = match (b % 0b01000000uy) / 0b00100000uy <: byte with
                                | 0b0uy -> PRIMITIVE
                                | 0b1uy -> CONSTRUCTED in
                let tag_value = b % 0b00100000uy in
                CUSTOM_TAG tag_class tag_form tag_value )

/// encode input bytes

let synth_asn1_tag_inverse a
= match a with
  | BOOLEAN      -> 0x01uy
  | INTEGER      -> 0x02uy
  | BIT_STRING   -> 0x03uy
  | OCTET_STRING -> 0x04uy
  | PRINTABLE_STRING -> 0x13uy
  | IA5_STRING   -> 0x16uy
  | ASN1_NULL    -> 0x05uy
  | OID          -> 0x06uy
  | Generalized_Time -> 0x18uy
  | SEQUENCE     -> 0x30uy
  | SET          -> 0x31uy
  | CUSTOM_TAG tag_class tag_form tag_value -> ( let b_tag_class = match tag_class with
                                                                     | APPLICATION      -> 0b01000000uy
                                                                     | CONTEXT_SPECIFIC -> 0b10000000uy
                                                                     | PRIVATE          -> 0b11000000uy in
                                                   let b_tag_form  = match tag_form with
                                                                     | PRIMITIVE   -> 0b000000uy
                                                                     | CONSTRUCTED -> 0b100000uy in
                                                   b_tag_class + b_tag_form + tag_value )

///
/// Parser
///
let parse_asn1_tag
= parse_u8
  `parse_filter`
  filter_asn1_tag
  `parse_synth`
  synth_asn1_tag

///
/// Serialier
///

let serialize_asn1_tag
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

///
/// Lemmas
///

/// Reveal the computation of parse
let lemma_parse_asn1_tag_unfold input
= parser_kind_prop_equiv parse_u8_kind parse_u8;
  parser_kind_prop_equiv parse_asn1_tag_kind parse_asn1_tag;
 (match parse parse_u8 input with
 | Some (x, 1) -> ( parse_u8_spec' input
                  ; parse_u8_spec  input
                  ; assert (x == input.[0]) )
 | None -> ());
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

/// Reveal the computation of serialization
let lemma_serialize_asn1_tag_unfold a
= serialize_u8_spec  (synth_asn1_tag_inverse a);
  serialize_u8_spec' (synth_asn1_tag_inverse a);
  serialize_synth_eq
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

/// Useful lemma about the length of serializations
let lemma_serialize_asn1_tag_size a
= parser_kind_prop_equiv parse_asn1_tag_kind parse_asn1_tag;
  lemma_serialize_asn1_tag_unfold a

///////////////////////////////////////////////////////
////  Specialied parser for a specific ASN1 type
///////////////////////////////////////////////////////

///
/// Aux functions
///

/// filter valid input bytes
let filter_asn1_tag_of_type a b
= b = (synth_asn1_tag_inverse a <: byte)

/// decode input bytes
noextract
let synth_asn1_tag_of_type
  (a: asn1_tag_t)
  (b: parse_filter_refine (filter_asn1_tag_of_type a))
: GTot (a': the_asn1_tag a {a' == synth_asn1_tag b})
= a

/// encode tags to bytes
let synth_asn1_tag_of_type_inverse a a'
= synth_asn1_tag_inverse a'

///
/// Parser
///
let parse_asn1_tag_of_type a
= parse_u8
  `parse_filter`
  filter_asn1_tag_of_type a
  `parse_synth`
  synth_asn1_tag_of_type a

///
/// Serializer
///
let serialize_asn1_tag_of_type a
= serialize_synth
  (* p1 *) (parse_u8
            `parse_filter`
            filter_asn1_tag_of_type a)
  (* f2 *) (synth_asn1_tag_of_type a)
  (* s1 *) (serialize_u8
            `serialize_filter`
            filter_asn1_tag_of_type a)
  (* g1 *) (synth_asn1_tag_of_type_inverse a)
  (* prf*) ()

///
/// Lemmas
///

/// Reveals the computations of parse
noextract
let lemma_parse_asn1_tag_of_type_unfold
  (a: asn1_tag_t)
  (input: bytes)
: Lemma (
  parse (parse_asn1_tag_of_type a) input ==
 (match parse parse_u8 input with
  | Some (x, consumed) -> if filter_asn1_tag_of_type a x then
                          ( Some (synth_asn1_tag_of_type a x, consumed) )
                          else
                          ( None )
  | None -> None) /\
 (Some? (parse (parse_asn1_tag_of_type a) input) ==>
   Seq.length input > 0 /\
   Some? (parse parse_u8 input) /\
   parse parse_u8 input == Some (input.[0], 1)))
= parser_kind_prop_equiv parse_u8_kind parse_u8;
  parser_kind_prop_equiv parse_asn1_tag_kind (parse_asn1_tag_of_type a);
 (match parse parse_u8 input with
 | Some (x, 1) -> ( parse_u8_spec' input
                  ; parse_u8_spec  input
                  ; assert (x == input.[0]) )
 | None -> ());
  parse_filter_eq
  (* p  *) (parse_u8)
  (* f  *) (filter_asn1_tag_of_type a)
  (* in *) (input);
  parse_synth_eq
  (* p1 *) (parse_u8
            `parse_filter`
            filter_asn1_tag_of_type a)
  (* f2 *) (synth_asn1_tag_of_type a)
  (* in *) (input)

/// Reveals the computation of serialize
let lemma_serialize_asn1_tag_of_type_unfold a a'
= serialize_u8_spec  (synth_asn1_tag_of_type_inverse a a');
  serialize_u8_spec' (synth_asn1_tag_of_type_inverse a a');
  serialize_synth_eq
  (* p1 *) (parse_u8
            `parse_filter`
            filter_asn1_tag_of_type a)
  (* f2 *) (synth_asn1_tag_of_type a)
  (* s1 *) (serialize_u8
            `serialize_filter`
            filter_asn1_tag_of_type a)
  (* g1 *) (synth_asn1_tag_of_type_inverse a)
  (* prf*) ()
  (* in *) (a')

/// Reveals the size of a serialization
let lemma_serialize_asn1_tag_of_type_size _a a
= parser_kind_prop_equiv parse_asn1_tag_kind (parse_asn1_tag_of_type _a);
  lemma_serialize_asn1_tag_of_type_unfold _a a
