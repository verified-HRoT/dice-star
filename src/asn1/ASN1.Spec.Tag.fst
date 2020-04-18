module ASN1.Spec.Tag

open LowParse.Spec.Base
open LowParse.Spec.Combinators
open LowParse.Spec.Int

open ASN1.Base

/// Generic
///
let filter_asn1_tag
  (b: byte)
: Ghost bool
  (requires True)
  (ensures fun r -> r == (b = 0x01uy || b = 0x04uy || b = 0x05uy || b = 0x30uy || b = 0x03uy || b = 0x02uy || b = 0x06uy))
= match b with
  | 0x01uy | 0x04uy | 0x05uy | 0x30uy | 0x03uy | 0x02uy | 0x06uy -> true
  | _ -> false

let synth_asn1_tag
  (b: parse_filter_refine filter_asn1_tag)
: Ghost asn1_type
  (requires True)
  (ensures fun a ->
    a == (match b with
          | 0x01uy -> BOOLEAN
          | 0x02uy -> INTEGER
          | 0x03uy -> BIT_STRING
          | 0x04uy -> OCTET_STRING
          | 0x05uy -> NULL
          | 0x06uy -> OID
          | 0x30uy -> SEQUENCE))
= match b with
  | 0x01uy -> BOOLEAN
  | 0x02uy -> INTEGER
  | 0x03uy -> BIT_STRING
  | 0x04uy -> OCTET_STRING
  | 0x05uy -> NULL
  | 0x06uy -> OID
  | 0x30uy -> SEQUENCE

let synth_asn1_tag_inverse
  (a: asn1_type)
: Ghost (b: parse_filter_refine filter_asn1_tag{a == synth_asn1_tag b})
  (requires True)
  (ensures fun b -> a == synth_asn1_tag b)
= match a with
  | BOOLEAN      -> 0x01uy
  | INTEGER      -> 0x02uy
  | BIT_STRING   -> 0x03uy
  | OCTET_STRING -> 0x04uy
  | NULL         -> 0x05uy
  | OID          -> 0x06uy
  | SEQUENCE     -> 0x30uy

let parse_asn1_tag_kind = strong_parser_kind 1 1 None
let parse_asn1_tag
: parser parse_asn1_tag_kind asn1_type
= parse_u8
  `parse_filter`
  filter_asn1_tag
  `parse_synth`
  synth_asn1_tag

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

/// Specialied
///
let filter_the_asn1_tag
  (a: asn1_type)
  (b: byte)
: Ghost bool
  (requires True)
  (ensures fun r -> (r <==> filter_asn1_tag b /\ synth_asn1_tag b == a))
= match a, b with
  | BOOLEAN     , 0x01uy
  | INTEGER     , 0x02uy
  | BIT_STRING  , 0x03uy
  | OCTET_STRING, 0x04uy
  | NULL        , 0x05uy
  | OID         , 0x06uy
  | SEQUENCE    , 0x30uy -> true
  | _ -> false

let synth_the_asn1_tag
  (a: asn1_type)
  (b: parse_filter_refine (filter_the_asn1_tag a))
: Ghost (the_asn1_type a)
  (requires True)
  (ensures fun a' -> (a' == synth_asn1_tag b))
= a

let synth_the_asn1_tag_inverse
  (a: asn1_type)
  (a': the_asn1_type a)
: Ghost (parse_filter_refine (filter_the_asn1_tag a))
  (requires True)
  (ensures fun b -> (b == synth_asn1_tag_inverse a'))
= synth_asn1_tag_inverse a'

let parse_the_asn1_tag
  (a: asn1_type)
: parser parse_asn1_tag_kind (the_asn1_type a)
= parse_u8
  `parse_filter`
  filter_the_asn1_tag a
  `parse_synth`
  synth_the_asn1_tag a

let parse_the_asn1_tag_unfold
  (a: asn1_type)
  (input: bytes)
: Lemma (
  parse (parse_the_asn1_tag a) input ==
 (match parse parse_u8 input with
  | Some (x, consumed) -> if filter_the_asn1_tag a x then
                          ( Some (synth_the_asn1_tag a x, consumed) )
                          else
                          ( None )
  | None -> None) /\
 (Some? (parse (parse_the_asn1_tag a) input) ==>
   Seq.length input > 0 /\
   Some? (parse parse_u8 input) /\
   parse parse_u8 input == Some (input.[0], 1)))
= parser_kind_prop_equiv parse_u8_kind parse_u8;
  parser_kind_prop_equiv parse_asn1_tag_kind (parse_the_asn1_tag a);
 (match parse parse_u8 input with
 | Some (x, 1) -> ( parse_u8_spec' input
                  ; parse_u8_spec  input
                  ; assert (x == input.[0]) )
 | None -> ());
  parse_filter_eq
  (* p  *) (parse_u8)
  (* f  *) (filter_the_asn1_tag a)
  (* in *) (input);
  parse_synth_eq
  (* p1 *) (parse_u8
            `parse_filter`
            filter_the_asn1_tag a)
  (* f2 *) (synth_the_asn1_tag a)
  (* in *) (input)

let serialize_the_asn1_tag
  (a: asn1_type)
: serializer (parse_the_asn1_tag a)
= serialize_synth
  (* p1 *) (parse_u8
            `parse_filter`
            filter_the_asn1_tag a)
  (* f2 *) (synth_the_asn1_tag a)
  (* s1 *) (serialize_u8
            `serialize_filter`
            filter_the_asn1_tag a)
  (* g1 *) (synth_the_asn1_tag_inverse a)
  (* prf*) ()

let serialize_the_asn1_tag_unfold
  (a: asn1_type)
  (a': the_asn1_type a)
: Lemma (
  serialize serialize_u8 (synth_the_asn1_tag_inverse a a')
  `Seq.equal`
  Seq.create 1 (synth_the_asn1_tag_inverse a a') /\
  serialize (serialize_the_asn1_tag a) a'
  `Seq.equal`
  serialize serialize_u8 (synth_the_asn1_tag_inverse a a'))
= serialize_u8_spec  (synth_the_asn1_tag_inverse a a');
  serialize_u8_spec' (synth_the_asn1_tag_inverse a a');
  serialize_synth_eq
  (* p1 *) (parse_u8
            `parse_filter`
            filter_the_asn1_tag a)
  (* f2 *) (synth_the_asn1_tag a)
  (* s1 *) (serialize_u8
            `serialize_filter`
            filter_the_asn1_tag a)
  (* g1 *) (synth_the_asn1_tag_inverse a)
  (* prf*) ()
  (* in *) (a')

