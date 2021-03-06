module ASN1.Spec.Value.BIT_STRING

open ASN1.Spec.Base
open LowParse.Spec.SeqBytes.Base

open ASN1.Base
open ASN1.Spec.Tag
open ASN1.Spec.Length

open FStar.Integers

module B32 = FStar.Bytes

(* NOTE: Read after `ASN1.Spec.Tag`, `ASN1.Spec.Length`, `ASN1.Spec.Value.BIT_STRING` *)

(* NOTE: This module defines:
         1) The ASN1 `BIT_STRING` Value Parser and Serializer
         2) The ASN1 `BIT_STRING` TLV Parser and Serializer

         And each part is organized as:
         1) Aux (ghost) functions with prefix `filter_` to filter out invalid input bytes
         2) Aux (ghost) functions with prefix `synth_` to decode the valid input bytes into our
            representation of BIT_STRING values. These functions are injective.
         3) Aux (ghost) functions with prefix `synth_` and suffix `_inverse` to encode our
            representation of BIT_STRING into bytes. These functions are the inverse of
            corresponding synth functions.
         4) Functions with the prefix `parse_` are parsers constructed using parser combinators and
            aux functions.
         5) Functions with the prefix `serialize_` are serializers constructed using serializer
            combinators and aux functions.
         6) Lemma with suffix `_unfold` reveals the computation of parser/serialzier.
         7) Lemma with suffix `_size` reveals the length of a serialization.
*)

/// TEST
///

// let bs_empty   : datatype_of_asn1_type BIT_STRING = (|1ul, 0ul, B32.empty_bytes |)
// let bs_0_unused: datatype_of_asn1_type BIT_STRING = (|2ul, 0ul, B32.create 1ul 0b1uy|)
// let bs_1_unused: datatype_of_asn1_type BIT_STRING = (|2ul, 1ul, B32.create 1ul 0b10uy|)
// let bs_2_unused: datatype_of_asn1_type BIT_STRING = (|2ul, 2ul, B32.create 1ul 0b100uy|)
// let bs_3_unused: datatype_of_asn1_type BIT_STRING = (|2ul, 3ul, B32.create 1ul 0b1000uy|)
// let bs_4_unused: datatype_of_asn1_type BIT_STRING = (|2ul, 4ul, B32.create 1ul 0b10000uy|)
// let bs_5_unused: datatype_of_asn1_type BIT_STRING = (|2ul, 5ul, B32.create 1ul 0b100000uy|)
// let bs_6_unused: datatype_of_asn1_type BIT_STRING = (|2ul, 6ul, B32.create 1ul 0b1000000uy|)
// let bs_7_unused: datatype_of_asn1_type BIT_STRING = (|2ul, 7ul, B32.create 1ul 0b10000000uy|)

(*
   Len = 1, unused = 0, bytes = []
   Len = 2, unused = x, bytes = [_]
*)

// let (.[]) = B32.index

/// filter valid input bytes
/// 1) if the length of input bytes is 1 (the minimal length), then the first and
///    the only byte, which represents the `unused_bits`, must be 0x00uy
/// 2) otherwise, the `unused_bits` must be in [0, 7] and the last byte's last
/// `unused_bits` bits must be zero.

let filter_asn1_bit_string l raw
= let unused_bits = raw.[0] in
  if l = 1 then
  ( unused_bits = 0uy )
  else
  ( let mask = normalize_term (pow2 (v unused_bits)) in
    0uy <= unused_bits && unused_bits <= 7uy &&
    (* x % 0b10..0 to check whether the last ... bits is 0 *)
    0 = normalize_term ((v raw.[l - 1]) % mask) )

/// Decode the valid input bytes into our representation of BIT_STRING,
/// which is a dependent tuple of `total length, unused_bits, octets`
let synth_asn1_bit_string l raw
= let unused_bits: n: asn1_int32 {0 <= v n /\ v n <= 7} = cast raw.[0] in
  let s32 = B32.hide (Seq.slice raw 1 l) in
  { bs_len         = u l;
    bs_unused_bits = unused_bits;
    bs_s           = s32 }

/// Prove our decode function is injective
#push-options "--z3rlimit 16"
noextract
let synth_asn1_bit_string_injective'
  (l: asn1_value_length_of_type BIT_STRING)
  (raw1 raw2: parse_filter_refine (filter_asn1_bit_string l))
: Lemma
  (requires synth_asn1_bit_string l raw1 == synth_asn1_bit_string l raw2)
  (ensures raw1 == raw2)
= Seq.lemma_split raw1 1;
  Seq.lemma_split raw2 1;
  assert (raw1 `Seq.equal` raw2)
#pop-options

noextract
let synth_asn1_bit_string_injective
  (l: asn1_value_length_of_type BIT_STRING)
: Lemma (
  synth_injective (synth_asn1_bit_string l)
)
= synth_injective_intro'
  (* f *) (synth_asn1_bit_string l)
  (*prf*) (synth_asn1_bit_string_injective' l)

/// Encode our representation of BIT_STRING into bytes
let synth_asn1_bit_string_inverse l value
= let raw = cast value.bs_unused_bits `Seq.cons` B32.reveal value.bs_s in
  let value' = synth_asn1_bit_string l raw in
  B32.extensionality value.bs_s value'.bs_s;
  raw

///
/// ASN1 BIT_STRING Value Parser
///
noextract
let parse_asn1_bit_string l
= synth_asn1_bit_string_injective l;
  parse_seq_flbytes l
  `parse_filter`
  filter_asn1_bit_string l
  `parse_synth`
  synth_asn1_bit_string l

///
/// ASN1 BIT_STRING Value Serialzier
///
let serialize_asn1_bit_string l
= serialize_synth
  (* p1 *) (parse_seq_flbytes l
            `parse_filter`
            filter_asn1_bit_string l)
  (* f2 *) (synth_asn1_bit_string l)
  (* s1 *) (serialize_seq_flbytes l
            `serialize_filter`
            filter_asn1_bit_string l)
  (* g1 *) (synth_asn1_bit_string_inverse l)
  (* prf*) (synth_asn1_bit_string_injective l)


///
/// Lemmas
///

/// Reveal the computation of parse
let lemma_parse_asn1_bit_string_unfold l input
= parser_kind_prop_equiv (get_parser_kind (parse_seq_flbytes l)) (parse_seq_flbytes l);
  parser_kind_prop_equiv (get_parser_kind (parse_asn1_bit_string l)) (parse_asn1_bit_string l);
  parse_filter_eq
  (* p *) (parse_seq_flbytes l)
  (* f *) (filter_asn1_bit_string l)
  (* in*) (input);
  synth_asn1_bit_string_injective l;
  parse_synth_eq
  (* p *) (parse_seq_flbytes l
           `parse_filter`
           filter_asn1_bit_string l)
  (* f *) (synth_asn1_bit_string l)
  (* in*) (input)

/// Reveal the computation of serialize
let lemma_serialize_asn1_bit_string_unfold l value
= serialize_synth_eq
  (* p1 *) (parse_seq_flbytes l
            `parse_filter`
            filter_asn1_bit_string l)
  (* f2 *) (synth_asn1_bit_string l)
  (* s1 *) (serialize_seq_flbytes l
            `serialize_filter`
            filter_asn1_bit_string l)
  (* g1 *) (synth_asn1_bit_string_inverse l)
  (* prf*) (synth_asn1_bit_string_injective l)
  (* val*) (value)

/// Reveal the length of a serialzation
let lemma_serialize_asn1_bit_string_size l value
= parser_kind_prop_equiv (parse_asn1_bit_string_kind l) (parse_asn1_bit_string l);
  lemma_serialize_asn1_bit_string_unfold l value

///////////////////////////////////////////////////////////
//// ASN1 `BIT_STRING` TLV Parser and Serializer
///////////////////////////////////////////////////////////

/// parser tag for the `tagged_union` combinators
let parser_tag_of_bit_string x
= (BIT_STRING, x.bs_len)

///
/// A pair of aux parser/serializer, which explicitly coerce the `BIT_STRING` value
/// between the subtype used by `BIT_STRING` value parser/serialzier and `BIT_STRING`
/// TLV parser/serializer.
///
/// NOTE: I found that have this aux parser explicitly defined will make the prove of
///       `_unfold` lemmas simpler.
///

/// Convert an `BIT_STRING` value from the subtype used by its value parser to the subtype
/// used by its TLV parser/serializer
/// (value : subtype_{value}) <: subtype_{TLV}
noextract
let synth_asn1_bit_string_V tag value
= value

/// Convert an `BIT_STRING` value from the subtype used by its TLV parser to the subtype
/// used by its value parser/serializer
/// (value : subtype_{TLV}) <: subtype_{value}
let synth_asn1_bit_string_V_inverse tag value'
= value'

///
/// Aux parser
///
let parse_asn1_bit_string_V tag
= (weak_kind_of_type BIT_STRING
   `weaken`
   parse_asn1_bit_string (v (snd tag)))
   `parse_synth`
   synth_asn1_bit_string_V tag

///
/// Aux serializer
///
let serialize_asn1_bit_string_V tag
= serialize_synth
  (* p1 *) (weak_kind_of_type BIT_STRING
            `weaken`
            parse_asn1_bit_string (v (snd tag)))
  (* f2 *) (synth_asn1_bit_string_V tag)
  (* s1 *) (weak_kind_of_type BIT_STRING
            `serialize_weaken`
            serialize_asn1_bit_string (v (snd tag)))
  (* g1 *) (synth_asn1_bit_string_V_inverse tag)
  (* prf*) ()

///
/// Lemmas
///

/// Reveal the computation of parse
let lemma_parse_asn1_bit_string_V_unfold tag input
= parse_synth_eq
  (* p1 *) (weak_kind_of_type BIT_STRING
            `weaken`
            parse_asn1_bit_string (v (snd tag)))
  (* f2 *) (synth_asn1_bit_string_V tag)
  (* in *) input

/// Reveal the computation of serialzation
noextract
let lemma_serialize_asn1_bit_string_V_unfold
  (tag: (the_asn1_tag BIT_STRING & asn1_value_int32_of_type BIT_STRING))
  (value: refine_with_tag parser_tag_of_bit_string tag)
: Lemma (
  serialize (serialize_asn1_bit_string_V tag) value ==
  serialize (serialize_asn1_bit_string (v (snd tag))) value
)
= serialize_synth_eq
  (* p1 *) (weak_kind_of_type BIT_STRING
            `weaken`
            parse_asn1_bit_string (v (snd tag)))
  (* f2 *) (synth_asn1_bit_string_V tag)
  (* s1 *) (weak_kind_of_type BIT_STRING
            `serialize_weaken`
            serialize_asn1_bit_string (v (snd tag)))
  (* g1 *) (synth_asn1_bit_string_V_inverse tag)
  (* prf*) ()
  (* in *) (value)


//////////////////////////////////////////////////////////

///
/// ASN1 `BIT_STRING` TLV Parser
///
let parse_asn1_bit_string_TLV
= parse_tagged_union
  (* pt *) (parse_asn1_tag_of_type BIT_STRING
            `nondep_then`
            parse_asn1_length_of_type BIT_STRING)
  (* tg *) (parser_tag_of_bit_string)
  (* p  *) (parse_asn1_bit_string_V)

///
/// ASN1 `BIT_STRING` TLV Serializer
///
#push-options "--initial_fuel 4"
let serialize_asn1_bit_string_TLV
= serialize_tagged_union
  (* st *) (serialize_asn1_tag_of_type BIT_STRING
            `serialize_nondep_then`
            serialize_asn1_length_of_type BIT_STRING)
  (* tg *) (parser_tag_of_bit_string)
  (* s  *) (serialize_asn1_bit_string_V)
#pop-options

///
/// Lemmas
///

/// Reveal the computation of parse
#restart-solver
#push-options "--z3rlimit 32"
let lemma_parse_asn1_bit_string_TLV_unfold input
= parser_kind_prop_equiv (get_parser_kind (parse_asn1_tag_of_type BIT_STRING)) (parse_asn1_tag_of_type BIT_STRING);
  parser_kind_prop_equiv (get_parser_kind (parse_asn1_length_of_type BIT_STRING)) (parse_asn1_length_of_type BIT_STRING);

  nondep_then_eq
  (* p1 *) (parse_asn1_tag_of_type BIT_STRING)
  (* p2 *) (parse_asn1_length_of_type BIT_STRING)
  (* in *) (input);

  let parser_tag = (parse_asn1_tag_of_type BIT_STRING
                    `nondep_then`
                    parse_asn1_length_of_type BIT_STRING) input in
  if Some? parser_tag then
  ( let Some (parser_tag, length) = parser_tag in
    lemma_parse_asn1_bit_string_V_unfold parser_tag (Seq.slice input length (Seq.length input)) );

  parse_tagged_union_eq
  (* pt *) (parse_asn1_tag_of_type BIT_STRING
            `nondep_then`
            parse_asn1_length_of_type BIT_STRING)
  (* tg *) (parser_tag_of_bit_string)
  (* p  *) (parse_asn1_bit_string_V)
  (* in *) (input)
#pop-options

/// Reveal the computation of serialize
#push-options "--z3rlimit 32"
let lemma_serialize_asn1_bit_string_TLV_unfold value
= serialize_nondep_then_eq
  (* s1 *) (serialize_asn1_tag_of_type BIT_STRING)
  (* s2 *) (serialize_asn1_length_of_type BIT_STRING)
  (* in *) (parser_tag_of_bit_string value);
  lemma_serialize_asn1_bit_string_V_unfold (parser_tag_of_bit_string value) value;
  serialize_tagged_union_eq
  (* st *) (serialize_asn1_tag_of_type BIT_STRING
            `serialize_nondep_then`
            serialize_asn1_length_of_type BIT_STRING)
  (* tg *) (parser_tag_of_bit_string)
  (* s  *) (serialize_asn1_bit_string_V)
  (* in *) (value)
#pop-options

/// Reveal the size of a serialzation
#push-options "--z3rlimit 16"
let lemma_serialize_asn1_bit_string_TLV_size value
= lemma_serialize_asn1_bit_string_TLV_unfold value;
  lemma_serialize_asn1_tag_of_type_size BIT_STRING BIT_STRING;
  lemma_serialize_asn1_length_size value.bs_len;
  serialize_asn1_length_of_type_eq BIT_STRING value.bs_len;
  lemma_serialize_asn1_bit_string_size (v value.bs_len) value
#pop-options
