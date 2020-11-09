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

/// filter valid input bytes

val filter_asn1_tag
  (b: byte)
: GTot bool

/// decode input bytes

val synth_asn1_tag
  (b: parse_filter_refine filter_asn1_tag)
: GTot asn1_tag_t

/// encode input bytes

val synth_asn1_tag_inverse
  (a: asn1_tag_t)
: GTot (b: parse_filter_refine filter_asn1_tag{a == synth_asn1_tag b})

inline_for_extraction noextract
let parse_asn1_tag_kind = strong_parser_kind 1 1 None

///
/// Parser
///
noextract val parse_asn1_tag : parser parse_asn1_tag_kind asn1_tag_t

///
/// Serialier
///
noextract val serialize_asn1_tag : serializer parse_asn1_tag

/// Lemmas

/// Reveal the computation of serialization

val lemma_serialize_asn1_tag_unfold
  (a: asn1_tag_t)
: Lemma (
  serialize serialize_u8 (synth_asn1_tag_inverse a)
  `Seq.equal`
  Seq.create 1 (synth_asn1_tag_inverse a) /\
  serialize serialize_asn1_tag a
  `Seq.equal`
  serialize serialize_u8 (synth_asn1_tag_inverse a))

/// Useful lemma about the length of serializations

val lemma_serialize_asn1_tag_size
  (a: asn1_tag_t)
: Lemma (
  Seq.length (serialize serialize_asn1_tag a) == 1)

///////////////////////////////////////////////////////
////  Specialied parser for a specific ASN1 type
///////////////////////////////////////////////////////

///
/// Aux functions
///

/// filter valid input bytes

val filter_asn1_tag_of_type
  (a: asn1_tag_t)
  (b: byte)
: GTot bool

/// decode input bytes

/// encode tags to bytes

val synth_asn1_tag_of_type_inverse
  (a: asn1_tag_t)
  (a': the_asn1_tag a)
: GTot (b: parse_filter_refine (filter_asn1_tag_of_type a) {b == synth_asn1_tag_inverse a})

///
/// Parser
///

noextract
val parse_asn1_tag_of_type
  (a: asn1_tag_t)
: parser parse_asn1_tag_kind (the_asn1_tag a)

noextract
val serialize_asn1_tag_of_type
  (a: asn1_tag_t)
  : serializer (parse_asn1_tag_of_type a)


/// Reveals the computation of serialize

val lemma_serialize_asn1_tag_of_type_unfold
  (a: asn1_tag_t)
  (a': the_asn1_tag a)
: Lemma (
  serialize serialize_u8 (synth_asn1_tag_of_type_inverse a a')
  `Seq.equal`
  Seq.create 1 (synth_asn1_tag_of_type_inverse a a') /\
  serialize (serialize_asn1_tag_of_type a) a'
  `Seq.equal`
  serialize serialize_u8 (synth_asn1_tag_of_type_inverse a a'))

/// Reveals the size of a serialization

val lemma_serialize_asn1_tag_of_type_size
  (_a: asn1_tag_t)
  (a : the_asn1_tag _a)
: Lemma (
  Seq.length (serialize (serialize_asn1_tag_of_type _a) a) == 1)
