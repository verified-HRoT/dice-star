module ASN1.Spec.Value.BigInteger

open ASN1.Spec.Base
open LowParse.Spec.SeqBytes.Base

open ASN1.Base
open ASN1.Spec.Tag
open ASN1.Spec.Length

open FStar.Integers

module B32 = FStar.Bytes

// let asn1_value_length_of_big_integer
// = l: asn1_length_t { 1 <= l /\ l <= asn1_length_max - 6}

let asn1_value_int32_of_big_integer
= LowParse.Spec.BoundedInt.bounded_int32 1 (asn1_length_max - 6)

let asn1_TLV_length_of_big_integer
= l: asn1_length_t { 3 <= l /\ l <= asn1_length_max }

let asn1_TLV_int32_of_big_integer
= LowParse.Spec.BoundedInt.bounded_int32 3 asn1_length_max

// unfold
// let valid_big_integer_as_octet_string_prop
//   (l: asn1_value_length_of_big_integer)
//   (x: big_integer_as_octet_string_t)
// : Type0
// = v (dfst x) > 0 /\
//   ( let (.[]) = B32.index in
//     if l = 1 then
//     ( v (dfst x) == l /\ (dsnd x).[0] < 0x80uy )
//     else if ((dsnd x).[0] >= 0x80uy) then
//     ( v (dfst x) == l - 1 )
//     else
//     ( v (dfst x) == l /\ (dsnd x).[0] > 0x00uy ) )

///
let filter_big_integer_as_octet_string
  (l: asn1_value_length_of_big_integer)
  (s: lbytes l)
: GTot bool
= l > 0 &&
  ( if (l = 1) then
    ( s.[0] < 0x80uy )
    else if (s.[0] = 0x00uy) then
    ( s.[1] >= 0x80uy )
    else
    ( s.[0] < 0x80uy ) )


noextract
let synth_big_integer_as_octet_string
  (l: asn1_value_length_of_big_integer)
  (s: parse_filter_refine (filter_big_integer_as_octet_string l))
: GTot (value: big_integer_as_octet_string_t
               { valid_big_integer_as_octet_string_prop l value })
= if (l = 1) then
  ( (|1ul, B32.hide s|) )
  else if (s.[0] = 0x00uy) then
  ( (|u (l - 1), B32.hide (Seq.slice s 1 l)|) )
  else
  ( (|u l, B32.hide s|) )

let lemma_synth_big_integer_as_octet_string_injective'
  (l: asn1_value_length_of_big_integer)
  (s s': parse_filter_refine (filter_big_integer_as_octet_string l))
: Lemma
  (requires synth_big_integer_as_octet_string l s == synth_big_integer_as_octet_string l s')
  (ensures s == s')
= if (l = 1) then
  ( () )
  else if (s.[0] = 0x00uy) then
  ( Seq.lemma_split s  1;
    Seq.lemma_split s' 1;
    assert (s `Seq.equal` s') )
  else
  ( () )

let lemma_synth_big_integer_as_octet_string_injective
  (l: asn1_value_length_of_big_integer)
: Lemma (
  synth_injective (synth_big_integer_as_octet_string l)
)
= synth_injective_intro'
  (* f *) (synth_big_integer_as_octet_string l)
  (*prf*) (lemma_synth_big_integer_as_octet_string_injective' l)

/// Encodes our representation of a OCTET_STRING into bytes
noextract
let synth_big_integer_as_octet_string_inverse
  (l: asn1_value_length_of_big_integer)
  (value: big_integer_as_octet_string_t {valid_big_integer_as_octet_string_prop l value})
: GTot (s32: parse_filter_refine (filter_big_integer_as_octet_string l)
            { value == synth_big_integer_as_octet_string l s32 })
= let (.[]) = B32.index in
  if l = 1 then
  ( B32.reveal (dsnd value) )
  else if (dsnd value).[0] >= 0x80uy then
  ( let s = Seq.create 1 0x00uy `Seq.append` B32.reveal (dsnd value) in
    B32.extensionality (dsnd value) (B32.hide (Seq.slice s 1 l));
    s )
  else
  ( B32.reveal (dsnd value) )

// inline_for_extraction noextract
let parse_big_integer_as_octet_string_kind (l: asn1_value_length_of_big_integer) = constant_size_parser_kind l

///
/// Parser
///
let parse_big_integer_as_octet_string
  (l: asn1_value_length_of_big_integer)
: parser (parse_big_integer_as_octet_string_kind l) (x: big_integer_as_octet_string_t {valid_big_integer_as_octet_string_prop l x})
= lemma_synth_big_integer_as_octet_string_injective l;
  parse_seq_flbytes l
  `parse_filter`
  filter_big_integer_as_octet_string l
  `parse_synth`
  synth_big_integer_as_octet_string l

///
/// Serializer
///
let serialize_big_integer_as_octet_string
  (l: asn1_value_length_of_big_integer)
: serializer (parse_big_integer_as_octet_string l)
= serialize_synth
  (* p1 *) (parse_seq_flbytes l
            `parse_filter`
            filter_big_integer_as_octet_string l)
  (* f2 *) (synth_big_integer_as_octet_string l)
  (* s1 *) (serialize_seq_flbytes l
            `serialize_filter`
            filter_big_integer_as_octet_string l)
  (* g1 *) (synth_big_integer_as_octet_string_inverse l)
  (* Prf*) (lemma_synth_big_integer_as_octet_string_injective l)

///
/// Lemmas
///

/// Reveal the computation of serialize
let lemma_serialize_big_integer_as_octet_string_unfold
  (l: asn1_value_length_of_big_integer)
  (value: get_parser_type (parse_big_integer_as_octet_string l))
: Lemma (
  serialize (serialize_big_integer_as_octet_string l) value ==
  serialize (serialize_seq_flbytes l) (synth_big_integer_as_octet_string_inverse l value))
= serialize_synth_eq
  (* p1 *) (parse_seq_flbytes l
            `parse_filter`
            filter_big_integer_as_octet_string l)
  (* f2 *) (synth_big_integer_as_octet_string l)
  (* s1 *) (serialize_seq_flbytes l
            `serialize_filter`
            filter_big_integer_as_octet_string l)
  (* g1 *) (synth_big_integer_as_octet_string_inverse l)
  (* Prf*) (lemma_synth_big_integer_as_octet_string_injective l)
  (* in *) (value)

/// Reveal the length of a serialzation
noextract
let lemma_serialize_big_integer_as_octet_string_size
  (l: asn1_value_length_of_big_integer)
  (value: get_parser_type (parse_big_integer_as_octet_string l))
: Lemma (
  Seq.length (serialize (serialize_big_integer_as_octet_string l) value) == l)
= lemma_serialize_big_integer_as_octet_string_unfold l value


///////////////////////////////////////////////////////////
//// ASN1 `OCTET_STRING` TLV Parser and Serializer
///////////////////////////////////////////////////////////

/// parser tag for the `tagged_union` combinators
let parser_tag_of_big_integer_as_octet_string
  (x: big_integer_as_octet_string_t)
: Tot (the_asn1_tag INTEGER & asn1_value_int32_of_big_integer)
= let (.[]) = B32.index in
  if ((dsnd x).[0] >= 0x80uy) then
  ( (INTEGER, dfst x + 1ul) )
  else
  ( (INTEGER, dfst x) )

open LowParse.Spec.DER
let parse_asn1_length_kind_of_big_integer
= parse_bounded_der_length32_kind 1 (asn1_length_max - 6)

let parse_asn1_length_of_big_integer
: parser parse_asn1_length_kind_of_big_integer asn1_value_int32_of_big_integer
= parse_asn1_length_of_bound 1 (asn1_length_max - 6)

let serialize_asn1_length_of_big_integer
: serializer (parse_asn1_length_of_big_integer)
= serialize_asn1_length_of_bound 1 (asn1_length_max - 6)

let weak_kind_of_big_integer
= strong_parser_kind 1 (asn1_length_max - 6) None

inline_for_extraction noextract
let parse_big_integer_as_octet_string_TLV_kind
: parser_kind
= parse_asn1_tag_kind
  `and_then_kind`
  parse_asn1_length_kind_of_big_integer
  `and_then_kind`
  weak_kind_of_big_integer

noextract
let synth_big_integer_as_octet_string_V
  (tag: (the_asn1_tag INTEGER & asn1_value_int32_of_big_integer))
  (value: big_integer_as_octet_string_t
         { valid_big_integer_as_octet_string_prop (v (snd tag)) value })
: GTot (refine_with_tag parser_tag_of_big_integer_as_octet_string tag)
= value

noextract inline_for_extraction
let synth_big_integer_as_octet_string_V_inverse
  (tag: (the_asn1_tag INTEGER & asn1_value_int32_of_big_integer))
  (value': refine_with_tag parser_tag_of_big_integer_as_octet_string tag)
: Tot (value: big_integer_as_octet_string_t
               { valid_big_integer_as_octet_string_prop (v (snd tag)) value /\
                 value' == synth_big_integer_as_octet_string_V tag value})
= value'


///
/// Aux parser
///
noextract
let parse_big_integer_as_octet_string_V
  (tag: (the_asn1_tag INTEGER & asn1_value_int32_of_big_integer))
: parser (weak_kind_of_big_integer) (refine_with_tag parser_tag_of_big_integer_as_octet_string tag)
= weak_kind_of_big_integer
  `weaken`
  parse_big_integer_as_octet_string (v (snd tag))
  `parse_synth`
  synth_big_integer_as_octet_string_V tag

///
/// Aux serializer
///
noextract
let serialize_big_integer_as_octet_string_V
  (tag: (the_asn1_tag INTEGER & asn1_value_int32_of_big_integer))
: serializer (parse_big_integer_as_octet_string_V tag)
= serialize_synth
  (* p1 *) (weak_kind_of_big_integer
            `weaken`
            parse_big_integer_as_octet_string (v (snd tag)))
  (* f2 *) (synth_big_integer_as_octet_string_V tag)
  (* s1 *) (weak_kind_of_big_integer
            `serialize_weaken`
            serialize_big_integer_as_octet_string (v (snd tag)))
  (* g1 *) (synth_big_integer_as_octet_string_V_inverse tag)
  (* prf*) ()

///
/// Lemmas
///

/// Reveal the computation of parse
noextract
let lemma_parse_big_integer_as_octet_string_V_unfold
  (tag: (the_asn1_tag INTEGER & asn1_value_int32_of_big_integer))
  (input: bytes)
: Lemma (
  parse (parse_big_integer_as_octet_string_V tag) input ==
 (match parse (parse_big_integer_as_octet_string (v (snd tag))) input with
  | None -> None
  | Some (value, consumed) ->  Some (synth_big_integer_as_octet_string_V tag value, consumed)))
= parse_synth_eq
  (* p1 *) (weak_kind_of_big_integer
            `weaken`
            parse_big_integer_as_octet_string (v (snd tag)))
  (* f2 *) (synth_big_integer_as_octet_string_V tag)
  (* in *) input

/// Reveal the computation of serialzation
noextract
let lemma_serialize_big_integer_as_octet_string_V_unfold
  (tag: (the_asn1_tag INTEGER & asn1_value_int32_of_big_integer))
  (value: refine_with_tag parser_tag_of_big_integer_as_octet_string tag)
: Lemma (
  serialize (serialize_big_integer_as_octet_string_V tag) value ==
  serialize (serialize_big_integer_as_octet_string (v (snd tag))) value
)
= serialize_synth_eq
  (* p1 *) (weak_kind_of_big_integer
            `weaken`
            parse_big_integer_as_octet_string (v (snd tag)))
  (* f2 *) (synth_big_integer_as_octet_string_V tag)
  (* s1 *) (weak_kind_of_big_integer
            `serialize_weaken`
            serialize_big_integer_as_octet_string (v (snd tag)))
  (* g1 *) (synth_big_integer_as_octet_string_V_inverse tag)
  (* prf*) ()
  (* in *) (value)


//////////////////////////////////////////////////////////

noextract
let parse_big_integer_as_octet_string_TLV
: parser parse_big_integer_as_octet_string_TLV_kind big_integer_as_octet_string_t
= parse_tagged_union
  (* pt *) (parse_asn1_tag_of_type INTEGER
            `nondep_then`
            parse_asn1_length_of_big_integer)
  (* tg *) (parser_tag_of_big_integer_as_octet_string)
  (* p  *) (parse_big_integer_as_octet_string_V)

///
/// Serializer
///
noextract
let serialize_big_integer_as_octet_string_TLV
: serializer parse_big_integer_as_octet_string_TLV
= serialize_tagged_union
  (* st *) (serialize_asn1_tag_of_type INTEGER
            `serialize_nondep_then`
            serialize_asn1_length_of_big_integer)
  (* tg *) (parser_tag_of_big_integer_as_octet_string)
  (* s  *) (serialize_big_integer_as_octet_string_V)

///
/// Lemmas
///

/// Reveal the computation of serialize
#push-options "--z3rlimit 32"
noextract
let lemma_serialize_big_integer_as_octet_string_TLV_unfold
  (value: big_integer_as_octet_string_t)
: Lemma (
  let tg = parser_tag_of_big_integer_as_octet_string value in
  serialize serialize_big_integer_as_octet_string_TLV value ==
  serialize (serialize_asn1_tag_of_type INTEGER) INTEGER
  `Seq.append`
  serialize (serialize_asn1_length_of_big_integer) (snd tg)
  `Seq.append`
  serialize (serialize_big_integer_as_octet_string (v (snd tg))) value
)
= serialize_nondep_then_eq
  (* s1 *) (serialize_asn1_tag_of_type INTEGER)
  (* s2 *) (serialize_asn1_length_of_big_integer)
  (* in *) (parser_tag_of_big_integer_as_octet_string value);
  lemma_serialize_big_integer_as_octet_string_V_unfold (parser_tag_of_big_integer_as_octet_string value) value;
  serialize_tagged_union_eq
  (* st *) (serialize_asn1_tag_of_type INTEGER
            `serialize_nondep_then`
            serialize_asn1_length_of_big_integer)
  (* tg *) (parser_tag_of_big_integer_as_octet_string)
  (* s  *) (serialize_big_integer_as_octet_string_V)
  (* in *) (value)
#pop-options

let length_of_big_integer_as_octet_string
  (x: big_integer_as_octet_string_t)
: GTot (asn1_TLV_length_of_big_integer)
= let tg = parser_tag_of_big_integer_as_octet_string x in
  1 + length_of_asn1_length (snd tg) + v (snd tg)

let len_of_big_integer_as_octet_string
  (x: big_integer_as_octet_string_t)
: Tot (len: asn1_TLV_int32_of_big_integer
            { v len == length_of_big_integer_as_octet_string x })
= let tg = parser_tag_of_big_integer_as_octet_string x in
  1ul + ASN1.Low.Length.len_of_asn1_length (snd tg) + (snd tg)

/// Reveal the size of a serialzation

#push-options "--z3rlimit 32 --fuel 0 --ifuel 0"
noextract
let lemma_serialize_big_integer_as_octet_string_TLV_size
  (value: big_integer_as_octet_string_t)
: Lemma (
  Seq.length (serialize serialize_big_integer_as_octet_string_TLV value) ==
  length_of_big_integer_as_octet_string value
)
= let tg = parser_tag_of_big_integer_as_octet_string value in
  lemma_serialize_asn1_tag_of_type_size INTEGER INTEGER;
  serialize_asn1_length_of_bound_eq 1 (asn1_length_max - 6) (snd tg);
  lemma_serialize_asn1_length_of_bound_size 1 (asn1_length_max - 6) (snd tg);
  lemma_serialize_big_integer_as_octet_string_size (v (snd tg)) value;
  lemma_serialize_big_integer_as_octet_string_TLV_unfold value
#pop-options
