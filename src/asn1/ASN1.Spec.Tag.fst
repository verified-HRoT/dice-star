module ASN1.Spec.Tag

open LowParse.Spec.Base
open LowParse.Spec.Combinators
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

/// filter valid input bytes
noextract
let filter_asn1_tag
  (b: byte)
: GTot bool
= match b with
  | 0x01uy | 0x04uy | 0x05uy | 0x30uy | 0x03uy | 0x02uy | 0x06uy -> true
  | _ -> false

/// decode input bytes
noextract
let synth_asn1_tag
  (b: parse_filter_refine filter_asn1_tag)
: GTot asn1_type
= match b with
  | 0x01uy -> BOOLEAN
  | 0x02uy -> INTEGER
  | 0x03uy -> BIT_STRING
  | 0x04uy -> OCTET_STRING
  | 0x05uy -> NULL
  | 0x06uy -> OID
  | 0x30uy -> SEQUENCE

/// encode input bytes
noextract
let synth_asn1_tag_inverse
  (a: asn1_type)
: GTot (b: parse_filter_refine filter_asn1_tag{a == synth_asn1_tag b})
= match a with
  | BOOLEAN      -> 0x01uy
  | INTEGER      -> 0x02uy
  | BIT_STRING   -> 0x03uy
  | OCTET_STRING -> 0x04uy
  | NULL         -> 0x05uy
  | OID          -> 0x06uy
  | SEQUENCE     -> 0x30uy

noextract
let parse_asn1_tag_kind = strong_parser_kind 1 1 None

///
/// Parser
///
noextract
let parse_asn1_tag
: parser parse_asn1_tag_kind asn1_type
= parse_u8
  `parse_filter`
  filter_asn1_tag
  `parse_synth`
  synth_asn1_tag

///
/// Serialier
///
noextract
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

///
/// Lemmas
///

/// Reveal the computation of parse
noextract
let parse_asn1_tag_unfold
  (input: bytes)
: Lemma (
  parse parse_asn1_tag input ==
 (match parse parse_u8 input with
  | Some (x, consumed) -> if filter_asn1_tag x then
                   ( Some (synth_asn1_tag x, consumed) )
                   else
                   ( None )
  | None -> None) /\
 (Some? (parse parse_asn1_tag input) ==>
   Seq.length input > 0 /\
   Some? (parse parse_u8 input) /\
   parse parse_u8 input == Some (input.[0], 1)))
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
noextract
let serialize_asn1_tag_unfold
  (a: asn1_type)
: Lemma (
  serialize serialize_u8 (synth_asn1_tag_inverse a)
  `Seq.equal`
  Seq.create 1 (synth_asn1_tag_inverse a) /\
  serialize serialize_asn1_tag a
  `Seq.equal`
  serialize serialize_u8 (synth_asn1_tag_inverse a))
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
noextract
let serialize_asn1_tag_size
  (a: asn1_type)
: Lemma (
  Seq.length (serialize serialize_asn1_tag a) == 1)
= parser_kind_prop_equiv parse_asn1_tag_kind parse_asn1_tag;
  serialize_asn1_tag_unfold a

///////////////////////////////////////////////////////
////  Specialied parser for a specific ASN1 type
///////////////////////////////////////////////////////

///
/// Aux functions
///

/// filter valid input bytes
noextract
let filter_asn1_tag_of_type
  (a: asn1_type)
  (b: byte)
: GTot bool
= match a, b with
  | BOOLEAN     , 0x01uy
  | INTEGER     , 0x02uy
  | BIT_STRING  , 0x03uy
  | OCTET_STRING, 0x04uy
  | NULL        , 0x05uy
  | OID         , 0x06uy
  | SEQUENCE    , 0x30uy -> true
  | _ -> false

/// decode input bytes
noextract
let synth_asn1_tag_of_type
  (a: asn1_type)
  (b: parse_filter_refine (filter_asn1_tag_of_type a))
: GTot (a': the_asn1_type a {a' == synth_asn1_tag b})
= a

/// encode tags to bytes
noextract
let synth_asn1_tag_of_type_inverse
  (a: asn1_type)
  (a': the_asn1_type a)
: GTot (b: parse_filter_refine (filter_asn1_tag_of_type a) {b == synth_asn1_tag_inverse a})
= synth_asn1_tag_inverse a'

///
/// Parser
///
noextract
let parse_asn1_tag_of_type
  (a: asn1_type)
: parser parse_asn1_tag_kind (the_asn1_type a)
= parse_u8
  `parse_filter`
  filter_asn1_tag_of_type a
  `parse_synth`
  synth_asn1_tag_of_type a

///
/// Serializer
///
noextract
let serialize_asn1_tag_of_type
  (a: asn1_type)
: serializer (parse_asn1_tag_of_type a)
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
let parse_asn1_tag_of_type_unfold
  (a: asn1_type)
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
noextract
let serialize_asn1_tag_of_type_unfold
  (a: asn1_type)
  (a': the_asn1_type a)
: Lemma (
  serialize serialize_u8 (synth_asn1_tag_of_type_inverse a a')
  `Seq.equal`
  Seq.create 1 (synth_asn1_tag_of_type_inverse a a') /\
  serialize (serialize_asn1_tag_of_type a) a'
  `Seq.equal`
  serialize serialize_u8 (synth_asn1_tag_of_type_inverse a a'))
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
noextract
let serialize_asn1_tag_of_type_size
  (_a: asn1_type)
  (a : the_asn1_type _a)
: Lemma (
  Seq.length (serialize (serialize_asn1_tag_of_type _a) a) == 1)
= parser_kind_prop_equiv parse_asn1_tag_kind (parse_asn1_tag_of_type _a);
  serialize_asn1_tag_of_type_unfold _a a
