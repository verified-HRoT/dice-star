module ASN1.Spec.Value.BigInteger

open ASN1.Spec.Base

open ASN1.Base
open ASN1.Spec.Tag
open ASN1.Spec.Length
open ASN1.Spec.Bytes32

open FStar.Integers

module B32 = FStar.Bytes

let lemma_synth_big_integer_as_octet_string_injective'
  (len: asn1_value_int32_of_big_integer)
  (s32 s32': parse_filter_refine (filter_big_integer_as_octet_string len))
: Lemma
  (requires synth_big_integer_as_octet_string len s32 == synth_big_integer_as_octet_string len s32')
  (ensures s32 == s32')
= if (v len = 1) then
  ( () )
  else if (s32 `B32.index` 0 = 0x00uy) then
  ( assert (B32.length s32 == B32.length s32');
    assert (s32' `B32.index` 0 == 0x00uy);
    assert (s32 `B32.index` 0 == s32' `B32.index` 0);
    assert (B32.slice s32 1ul len `B32.equal` B32.slice s32' 1ul len);
    assert (forall (i: UInt32.t { 1 <= v i /\ v i < v (B32.length s32 )}). s32  `B32.get` i == B32.slice s32  1ul len `B32.get` (i - 1ul) );
    assert (forall (i: UInt32.t { 1 <= v i /\ v i < v (B32.length s32')}). s32' `B32.get` i == B32.slice s32' 1ul len `B32.get` (i - 1ul) );
    assert (s32 `B32.equal` s32');
    B32.extensionality s32 s32' )
  else
  ( () )

let lemma_synth_big_integer_as_octet_string_injective len
= synth_injective_intro'
  (* f *) (synth_big_integer_as_octet_string len)
  (*prf*) (lemma_synth_big_integer_as_octet_string_injective' len)

let parse_big_integer_as_octet_string len
= lemma_synth_big_integer_as_octet_string_injective len;
  parse_flbytes32 len
  `parse_filter`
  filter_big_integer_as_octet_string len
  `parse_synth`
  synth_big_integer_as_octet_string len

let serialize_big_integer_as_octet_string len
= serialize_synth
  (* p1 *) (parse_flbytes32 len
            `parse_filter`
            filter_big_integer_as_octet_string len)
  (* f2 *) (synth_big_integer_as_octet_string len)
  (* s1 *) (serialize_flbytes32 len
            `serialize_filter`
            filter_big_integer_as_octet_string len)
  (* g1 *) (synth_big_integer_as_octet_string_inverse len)
  (* Prf*) (lemma_synth_big_integer_as_octet_string_injective len)

let lemma_serialize_big_integer_as_octet_string_unfold len value
= serialize_synth_eq
  (* p1 *) (parse_flbytes32 len
            `parse_filter`
            filter_big_integer_as_octet_string len)
  (* f2 *) (synth_big_integer_as_octet_string len)
  (* s1 *) (serialize_flbytes32 len
            `serialize_filter`
            filter_big_integer_as_octet_string len)
  (* g1 *) (synth_big_integer_as_octet_string_inverse len)
  (* Prf*) (lemma_synth_big_integer_as_octet_string_injective len)
  (* in *) (value)

let lemma_serialize_big_integer_as_octet_string_size len value
= lemma_serialize_big_integer_as_octet_string_unfold len value

noextract
let synth_big_integer_as_octet_string_V
  (tag: (the_asn1_tag INTEGER & asn1_value_int32_of_big_integer))
  (value: big_integer_as_octet_string_t
         { valid_big_integer_as_octet_string_prop (snd tag) value })
: GTot (refine_with_tag parser_tag_of_big_integer_as_octet_string tag)
= value

noextract inline_for_extraction
let synth_big_integer_as_octet_string_V_inverse
  (tag: (the_asn1_tag INTEGER & asn1_value_int32_of_big_integer))
  (value': refine_with_tag parser_tag_of_big_integer_as_octet_string tag)
: Tot (value: big_integer_as_octet_string_t
               { valid_big_integer_as_octet_string_prop (snd tag) value /\
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
  parse_big_integer_as_octet_string (snd tag)
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
            parse_big_integer_as_octet_string (snd tag))
  (* f2 *) (synth_big_integer_as_octet_string_V tag)
  (* s1 *) (weak_kind_of_big_integer
            `serialize_weaken`
            serialize_big_integer_as_octet_string (snd tag))
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
 (match parse (parse_big_integer_as_octet_string (snd tag)) input with
  | None -> None
  | Some (value, consumed) ->  Some (synth_big_integer_as_octet_string_V tag value, consumed)))
= parse_synth_eq
  (* p1 *) (weak_kind_of_big_integer
            `weaken`
            parse_big_integer_as_octet_string (snd tag))
  (* f2 *) (synth_big_integer_as_octet_string_V tag)
  (* in *) input

/// Reveal the computation of serialzation
noextract
let lemma_serialize_big_integer_as_octet_string_V_unfold
  (tag: (the_asn1_tag INTEGER & asn1_value_int32_of_big_integer))
  (value: refine_with_tag parser_tag_of_big_integer_as_octet_string tag)
: Lemma (
  serialize (serialize_big_integer_as_octet_string_V tag) value ==
  serialize (serialize_big_integer_as_octet_string (snd tag)) value
)
= serialize_synth_eq
  (* p1 *) (weak_kind_of_big_integer
            `weaken`
            parse_big_integer_as_octet_string (snd tag))
  (* f2 *) (synth_big_integer_as_octet_string_V tag)
  (* s1 *) (weak_kind_of_big_integer
            `serialize_weaken`
            serialize_big_integer_as_octet_string (snd tag))
  (* g1 *) (synth_big_integer_as_octet_string_V_inverse tag)
  (* prf*) ()
  (* in *) (value)


//////////////////////////////////////////////////////////

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
let lemma_serialize_big_integer_as_octet_string_TLV_unfold
  (value: big_integer_as_octet_string_t)
: Lemma (
  let tg = parser_tag_of_big_integer_as_octet_string value in
  serialize serialize_big_integer_as_octet_string_TLV value ==
  serialize (serialize_asn1_tag_of_type INTEGER) INTEGER
  `Seq.append`
  serialize (serialize_asn1_length_of_big_integer) (snd tg)
  `Seq.append`
  serialize (serialize_big_integer_as_octet_string (snd tg)) value
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

// let length_of_big_integer_as_octet_string
//   (x: big_integer_as_octet_string_t)
// : GTot (asn1_TLV_length_of_big_integer)
// = let tg = parser_tag_of_big_integer_as_octet_string x in
//   1 + length_of_asn1_length (snd tg) + v (snd tg)

// let len_of_big_integer_as_octet_string
//   (x: big_integer_as_octet_string_t)
// : Tot (len: asn1_TLV_int32_of_big_integer
//             { v len == length_of_big_integer_as_octet_string x })
// = let tg = parser_tag_of_big_integer_as_octet_string x in
//   1ul + ASN1.Low.Length.len_of_asn1_length (snd tg) + (snd tg)

/// Reveal the size of a serialzation

#push-options "--z3rlimit 32 --fuel 0 --ifuel 0"
let lemma_serialize_big_integer_as_octet_string_TLV_size value
= let tg = parser_tag_of_big_integer_as_octet_string value in
  lemma_serialize_asn1_tag_of_type_size INTEGER INTEGER;
  serialize_asn1_length_of_bound_eq 1 (asn1_length_max - 6) (snd tg);
  lemma_serialize_asn1_length_of_bound_size 1 (asn1_length_max - 6) (snd tg);
  lemma_serialize_big_integer_as_octet_string_size (snd tg) value;
  lemma_serialize_big_integer_as_octet_string_TLV_unfold value
#pop-options
