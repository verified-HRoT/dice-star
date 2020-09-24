module ASN1.Spec.Value.INTEGER

open ASN1.Spec.Base
open LowParse.Spec.Int
open LowParse.Spec.SeqBytes.Base

open ASN1.Base
open ASN1.Spec.Tag
open ASN1.Spec.Length

module E = FStar.Endianness
open FStar.Integers

(* NOTE: Read after `ASN1.Spec.Tag`, `ASN1.Spec.Length` *)

(* NOTE: This module defines:
         1) The ASN1 `INTEGER` Value Parser and Serializer
         2) The ASN1 `INTEGER` TLV Parser and Serializer

         And each part is organized as:
         1) Aux (ghost) functions with prefix `filter_` to filter out invalid input bytes
         2) Aux (ghost) functions with prefix `synth_` to decode the valid input bytes into our
            representation of INTEGER values. These functions are injective.
         3) Aux (ghost) functions with prefix `synth_` and suffix `_inverse` to encode our
            representation of INTEGER into bytes. These functions are the inverse of
            corresponding synth functions.
         4) Functions with the prefix `parse_` are parsers constructed using parser combinators and
            aux functions.
         5) Functions with the prefix `serialize_` are serializers constructed using serializer
            combinators and aux functions.
         6) Lemma with suffix `_unfold` reveals the computation of parser/serialzier.
         7) Lemma with suffix `_size` reveals the length of a serialization.
*)

(*
NOTE: 1. Negative: `**p & 0x80 == 0`, reject
      2. Zero    : as `[0x02; 0x01; 0x00]` for INTEGER or `[0x0A; 0x01; 0x00]` fir ENUMERATED tags
      3. Positive: if the most significant bit of a positive integer is `1`, then add a leading zero.

NOTE: MbedTLS's implementation seems allow arbitrary leading zeros. We only allow one leading zero for now.
NOTE: We only allow at most 4-byte positive integers ([0, 0x7FFFFFFF]). If an integer is encoded into 5 bytes with a leading
      zero, then it must be a negative integer.
*)

//////////////////////////////////////////////////////////////////////
////       ASN1 `INTEGER` Value Parser/Serializer
//////////////////////////////////////////////////////////////////////

/// filters the valid input bytes accoring to the encoding rule
/// 1. valid length of input bytes is [1, 4]
/// 2. only positive integers, whether
///    a) the most significant bit is `0` (the first byte is less than 0x80uy/0b10000000uy), or
///    b) the first byte is a leading zero 0x00uy and the second byte's most significant bit is `1`
///       (the second byte is greater then or equal to 0x80uy/0b10000000uy)
let filter_asn1_integer l s
= match l with
  | 1 -> (* 1-byte integer with the most-significant bit `0` *)
         ( s.[0] < 0x80uy )

  | 2 -> (* 1-byte integer with the most-significant bit `1` *)
         if s.[0] = 0x00uy then
         ( s.[1] >= 0x80uy )

         (* 2-byte integer with the most-significant bit `0` *)
         else
         ( s.[0] < 0x80uy )

  | 3 -> (* 2-byte integer with the most-significant bit `1` *)
         if s.[0] = 0x00uy then
         ( s.[1] >= 0x80uy )

         (* 3-byte integer with the most-significant bit `0` *)
         else
         ( s.[0] < 0x80uy )

  | 4 -> (* 3-byte integer with the most-significant bit `1` *)
         if s.[0] = 0x00uy then
         ( s.[1] >= 0x80uy )

         (* 4-byte integer with the most-significant bit `0` *)
         else
         ( s.[0] < 0x80uy )

/// Length computation function/specification for a `INTEGER` value's serialization
// let length_of_asn1_integer value
// = let vx = v #(Signed W32) value in
//   if      0         <= vx && vx <= 0x7F      then
//   ( 1 )
//   else if 0x7F       < vx && vx <= 0xFF       then
//   ( 2 )
//   else if 0xFF       < vx && vx <= 0x7FFF     then
//   ( 2 )
//   else if 0x7FFF     < vx && vx <= 0xFFFF     then
//   ( 3 )
//   else if 0xFFFF     < vx && vx <= 0x7FFFFF   then
//   ( 3 )
//   else if 0x7FFFFF   < vx && vx <= 0xFFFFFF   then
//   ( 4 )
//   else if 0xFFFFFF   < vx && vx <= 0x7FFFFFFF then
//   ( 4 )

(* NOTE: Why this function signature will not pass type check when
         `datatype_of_asn1_type` is marked as `unfold`? *)
(* NOTE: Why I must explicitly provide #(Signed W32) everywhere? *)

/// Decode the valid input bytes to our represenation of ASN1 `INTEGER` value,
/// which is a _positive_ _signed_ 32-bit integer
/// 1) If the first byte is less then 0x80uy, then just decode it as an integer (in Big-Endian)
/// 2) If the first byte is a leading zero, then truncate it and decode the rest bytes as an
///    integer (in Big-Endian)
#restart-solver
#push-options "--z3rlimit 128"
noextract
let synth_asn1_integer l s
= match l with
  | 1 -> (* 1-byte integer with the most-significant bit `0` *)
         ( assert_norm (s.[0] < 0x80uy)
         ; E.lemma_be_to_n_is_bounded s
         ; E.reveal_be_to_n s
         ; assert_norm (Int.size (E.be_to_n s) 32)
         ; let value = u #(Signed W32) (E.be_to_n s) in
           assert_norm (0x00l <= value /\ value <= 0x7Fl)
         ; value )
  | 2 -> (* 1-byte integer with the most-significant bit `1` *)
         if s.[0] = 0x00uy then
         ( let s = Seq.slice s 1 l in
           assert_norm (s.[0] >= 0x80uy)
         ; E.lemma_be_to_n_is_bounded s
         ; E.reveal_be_to_n s
         ; assert_norm (Int.size (E.be_to_n s) 32)
         ; let value = u #(Signed W32) (E.be_to_n s) in
           assert_norm (0x7Fl < value /\ value <= 0xFFl)
         ; value )

         (* 2-byte integer with the most-significant bit `0` *)
         else
         ( assert_norm (s.[0] < 0x80uy)
         ; E.lemma_be_to_n_is_bounded s
         ; E.reveal_be_to_n s
         ; E.reveal_be_to_n (Seq.slice s 0 1)
         ; assert_norm (Int.size (E.be_to_n s) 32)
         ; let value = u #(Signed W32) (E.be_to_n s) in
           assert_norm (0xFFl < value /\ value <= 0x7FFFl)
         ; value )

  | 3 -> (* 2-byte integer with the most-significant bit `1` *)
         if s.[0] = 0x00uy then
         ( let s = Seq.slice s 1 l in
           assert_norm (s.[0] >= 0x80uy)
         ; E.lemma_be_to_n_is_bounded s
         ; E.reveal_be_to_n s
         ; E.reveal_be_to_n (Seq.slice s 0 1)
         ; assert_norm (Int.size (E.be_to_n s) 32)
         ; let value = u #(Signed W32) (E.be_to_n s) in
           assert_norm (0x7FFFl < value /\ value <= 0xFFFFl)
         ; value )

         (* 3-byte integer with the most-significant bit `0` *)
         else
         ( assert_norm (s.[0] < 0x80uy)
         ; E.lemma_be_to_n_is_bounded s
         ; E.reveal_be_to_n s
         ; E.reveal_be_to_n (Seq.slice s 0 2)
         ; E.reveal_be_to_n (Seq.slice s 0 1)
         ; assert_norm (Int.size (E.be_to_n s) 32)
         ; let value = u #(Signed W32) (E.be_to_n s) in
           assert_norm (0xFFFFl < value /\ value <= 0x7FFFFFl)
         ; value )

  | 4 -> (* 3-byte integer with the most-significant bit `1` *)
         if s.[0] = 0x00uy then
         ( let s = Seq.slice s 1 l in
           assert_norm (s.[0] >= 0x80uy)
         ; E.lemma_be_to_n_is_bounded s
         ; E.reveal_be_to_n s
         ; E.reveal_be_to_n (Seq.slice s 0 2)
         ; E.reveal_be_to_n (Seq.slice s 0 1)
         ; assert_norm (Int.size (E.be_to_n s) 32)
         ; let value = u #(Signed W32) (E.be_to_n s) in
           assert_norm (0x7FFFFFl < value /\ value <= 0xFFFFFFl)
         ; value )

         (* 4-byte integer with the most-significant bit `0` *)
         else
         ( assert_norm (s.[0] < 0x80uy)
         ; E.lemma_be_to_n_is_bounded s
         ; E.reveal_be_to_n s
         ; E.reveal_be_to_n (Seq.slice s 0 3)
         ; E.reveal_be_to_n (Seq.slice s 0 2)
         ; E.reveal_be_to_n (Seq.slice s 0 1)
         ; assert_norm (Int.size (E.be_to_n s) 32)
         ; let value = u #(Signed W32) (E.be_to_n s) in
           assert_norm (0xFFFFFFl < value /\ value <= 0x7FFFFFFFl)
         ; value )
#pop-options


/// Encode an integre accoding to the encoding rule
#push-options "--z3rlimit 128 --max_fuel 0 --max_ifuel 0"
noextract
let synth_asn1_integer_inverse l value
= let vx = v #(Signed W32) value in

  (* 1-byte integer with the most-significant bit `0` *)
  if      (0         <= vx && vx <= 0x7F      ) then
  ( assert_norm (vx < pow2 (8 * 1 - 1) /\
                 vx < pow2 (8 * 1))
  ; let s = E.n_to_be 1 vx in
    E.reveal_be_to_n s
  ; s )

  (* 1-byte integer with the most-significant bit `1` *)
  else if (0x7F       < vx && vx <= 0xFF      ) then
  ( assert_norm (vx < pow2 (8 * 1))
  ; let s = E.n_to_be 1 vx in
    E.reveal_be_to_n s
  ; let s = 0x00uy `Seq.cons` s in
    E.lemma_be_to_n_is_bounded (Seq.slice s 1 2)
  ; E.reveal_be_to_n (Seq.slice s 1 2)
  ; assert_norm (Int.size (E.be_to_n (Seq.slice s 1 2)) 32)
  ; assert_norm (synth_asn1_integer l s == value)
  ; s )

  (* 2-byte integer with the most-significant bit `0` *)
  else if (0xFF       < vx && vx <= 0x7FFF    ) then
  ( assert_norm (vx < pow2 (8 * 2 - 1) /\
                 vx < pow2 (8 * 2))
  ; let s = E.n_to_be 2 vx in
    E.reveal_be_to_n s
  ; E.reveal_be_to_n (Seq.slice s 0 1)
  ; s )

  (* 2-byte integer with the most-significant bit `1` *)
  else if (0x7FFF     < vx && vx <= 0xFFFF    ) then
  ( assert_norm (vx < pow2 (8 * 2))
  ; let s = E.n_to_be 2 vx in
    E.reveal_be_to_n s
  ; E.reveal_be_to_n (Seq.slice s 0 1)
  ; let s = 0x00uy `Seq.cons` s in
    E.lemma_be_to_n_is_bounded (Seq.slice s 1 3)
  ; E.reveal_be_to_n (Seq.slice s 1 3)
  ; E.reveal_be_to_n (Seq.slice s 1 2)
  ; assert_norm (Int.size (E.be_to_n (Seq.slice s 1 3)) 32)
  ; assert_norm (synth_asn1_integer l s == value)
  ; s )

  (* 3-byte integer with the most-significant bit `0` *)
  else if (0xFFFF      < vx && vx <= 0x7FFFFF  ) then
  ( assert_norm (vx < pow2 (8 * 3 - 1) /\
                 vx < pow2 (8 * 3))
  ; let s = E.n_to_be 3 vx in
    E.reveal_be_to_n s
  ; E.reveal_be_to_n (Seq.slice s 0 2)
  ; E.reveal_be_to_n (Seq.slice s 0 1)
  ; s )

  (* 3-byte integer with the most-significant bit `1` *)
  else if (0x7FFFFF   < vx && vx <= 0xFFFFFF  ) then
  ( assert_norm (vx < pow2 (8 * 3))
  ; let s = E.n_to_be 3 vx in
    E.reveal_be_to_n s
  ; E.reveal_be_to_n (Seq.slice s 0 2)
  ; E.reveal_be_to_n (Seq.slice s 0 1)
  ; let s = 0x00uy `Seq.cons` s in
    E.lemma_be_to_n_is_bounded (Seq.slice s 1 4)
  ; E.reveal_be_to_n (Seq.slice s 1 4)
  ; E.reveal_be_to_n (Seq.slice s 1 3)
  ; E.reveal_be_to_n (Seq.slice s 1 2)
  ; assert_norm (Int.size (E.be_to_n (Seq.slice s 1 4)) 32)
  ; assert_norm (synth_asn1_integer l s == value)
  ; s )

  (* 4-byte integer with the most-significant bit `0` *)
  else if (0xFFFFFF    < vx && vx <= 0x7FFFFFFF) then
  ( assert_norm (vx < pow2 (8 * 4 - 1) /\
                 vx < pow2 (8 * 4))
  ; let s = E.n_to_be 4 vx in
    E.reveal_be_to_n s
  ; E.reveal_be_to_n (Seq.slice s 0 3)
  ; E.reveal_be_to_n (Seq.slice s 0 2)
  ; E.reveal_be_to_n (Seq.slice s 0 1)
  ; s )

  (* Out of the range of positive 32-bit integer [0, 0x7FFFFFFF], unreachable *)
  else
  ( false_elim () )
#pop-options

/// Prove that the our decoding function is injective when there is a leading zero
/// in the input bytes
#push-options "--z3rlimit 192"
let synth_asn1_integer_injective_with_leading_zero l s1 s2
= match l with
  | 1 -> ( E.lemma_be_to_n_is_bounded s1
         ; E.lemma_be_to_n_is_bounded s2
         ; assert_norm (v (u #(Signed W32) (E.be_to_n s1)) == E.be_to_n s1)
         ; assert_norm (v (u #(Signed W32) (E.be_to_n s2)) == E.be_to_n s2)
         ; assert_norm (E.be_to_n s1 == E.be_to_n s2)
         ; E.be_to_n_inj s1 s2 )
  | 2 -> ( let value1 = synth_asn1_integer l s1 in
           assert_norm (s1.[1] >= 0x80uy)
         ; E.lemma_be_to_n_is_bounded (Seq.slice s1 1 2)
         ; E.reveal_be_to_n (Seq.slice s1 1 2)
         ; assert_norm (Int.size (E.be_to_n (Seq.slice s1 1 2)) 32)
         ; assert_norm (value1 == u #(Signed W32) (E.be_to_n (Seq.slice s1 1 2)))
         ; assert (0x7Fl < value1 /\ value1 <=0xFFl)
         ; let value2 = synth_asn1_integer l s2 in
           if s2.[0] = 0x00uy then
           ( E.reveal_be_to_n (Seq.slice s2 1 2)
           ; E.be_to_n_inj (Seq.slice s1 1 2) (Seq.slice s2 1 2) )
           else
           ( assert_norm (s2.[0] < 0x80uy)
           ; E.lemma_be_to_n_is_bounded s2
           ; E.reveal_be_to_n s2
           ; E.reveal_be_to_n (Seq.slice s2 0 1)
           ; assert_norm (Int.size (E.be_to_n s2) 32)
           ; assert_norm (value2 == u #(Signed W32) (E.be_to_n s2))
           ; assert_norm (value1 == value2)
           ; assert_norm (value2 > 0xFFl)
           ; false_elim () ) )
  | 3 -> ( let value1 = synth_asn1_integer l s1 in
           assert_norm (s1.[1] >= 0x80uy)
         ; E.lemma_be_to_n_is_bounded (Seq.slice s1 1 3)
         ; E.reveal_be_to_n (Seq.slice s1 1 3)
         ; E.reveal_be_to_n (Seq.slice s1 1 2)
         ; assert_norm (Int.size (E.be_to_n (Seq.slice s1 1 3)) 32)
         ; assert_norm (value1 == u #(Signed W32) (E.be_to_n (Seq.slice s1 1 3)))
         ; assert (0x7FFFl < value1 /\ value1 <=0xFFFFl)
         ; let value2 = synth_asn1_integer l s2 in
           if s2.[0] = 0x00uy then
           ( E.reveal_be_to_n (Seq.slice s2 1 3)
           ; E.reveal_be_to_n (Seq.slice s2 1 2)
           ; E.be_to_n_inj (Seq.slice s1 1 3) (Seq.slice s2 1 3) )
           else
           ( assert_norm (s2.[0] < 0x80uy)
           ; E.lemma_be_to_n_is_bounded s2
           ; E.reveal_be_to_n s2
           ; E.reveal_be_to_n (Seq.slice s2 0 2)
           ; E.reveal_be_to_n (Seq.slice s2 0 1)
           ; assert_norm (Int.size (E.be_to_n s2) 32)
           ; assert_norm (value2 == u #(Signed W32) (E.be_to_n s2))
           ; assert_norm (value1 == value2)
           ; assert_norm (value2 > 0xFFFFl)
           ; false_elim () ) )
  | 4 -> ( let value1 = synth_asn1_integer l s1 in
           assert_norm (s1.[1] >= 0x80uy)
         ; E.lemma_be_to_n_is_bounded (Seq.slice s1 1 4)
         ; E.reveal_be_to_n (Seq.slice s1 1 4)
         ; E.reveal_be_to_n (Seq.slice s1 1 3)
         ; E.reveal_be_to_n (Seq.slice s1 1 2)
         ; assert_norm (Int.size (E.be_to_n (Seq.slice s1 1 4)) 32)
         ; assert_norm (value1 == u #(Signed W32) (E.be_to_n (Seq.slice s1 1 4)))
         ; assert (0x7FFFFFl < value1 /\ value1 <=0xFFFFFFl)
         ; let value2 = synth_asn1_integer l s2 in
           if s2.[0] = 0x00uy then
           ( E.reveal_be_to_n (Seq.slice s2 1 4)
           ; E.reveal_be_to_n (Seq.slice s2 1 3)
           ; E.reveal_be_to_n (Seq.slice s2 1 2)
           ; E.be_to_n_inj (Seq.slice s1 1 4) (Seq.slice s2 1 4) )
           else
           ( assert_norm (s2.[0] < 0x80uy)
           ; E.lemma_be_to_n_is_bounded s2
           ; E.reveal_be_to_n s2
           ; E.reveal_be_to_n (Seq.slice s2 0 3)
           ; E.reveal_be_to_n (Seq.slice s2 0 2)
           ; E.reveal_be_to_n (Seq.slice s2 0 1)
           ; assert_norm (Int.size (E.be_to_n s2) 32)
           ; assert_norm (value2 == u #(Signed W32) (E.be_to_n s2))
           ; assert_norm (value1 == value2)
           ; assert_norm (value2 > 0xFFFFFFl)
           ; false_elim () ) )
#pop-options

/// Prove that the our decoding function is injective when there is no leading zero
/// in the input bytes
#push-options "--z3rlimit 128"
let synth_asn1_integer_injective_without_leading_zero l s1 s2
= match l with
  | 4 -> ( assert_norm (s1.[0] < 0x80uy /\ s2.[0] < 0x80uy)
         ; E.lemma_be_to_n_is_bounded s1
         ; E.lemma_be_to_n_is_bounded s2
         ; E.reveal_be_to_n s1
         ; E.reveal_be_to_n (Seq.slice s1 0 3)
         ; E.reveal_be_to_n (Seq.slice s1 0 2)
         ; E.reveal_be_to_n (Seq.slice s1 0 1)
         ; E.reveal_be_to_n s2
         ; E.reveal_be_to_n (Seq.slice s2 0 3)
         ; E.reveal_be_to_n (Seq.slice s2 0 2)
         ; E.reveal_be_to_n (Seq.slice s2 0 1)
         ; assert_norm (Int.size (E.be_to_n s1) 32)
         ; assert_norm (Int.size (E.be_to_n s2) 32)
         ; assert_norm (v (u #(Signed W32) (E.be_to_n s1)) == E.be_to_n s1)
         ; assert_norm (v (u #(Signed W32) (E.be_to_n s2)) == E.be_to_n s2)
         ; assert_norm (E.be_to_n s1 == E.be_to_n s2)
         ; E.be_to_n_inj s1 s2 )
  | _ -> ( assert_norm (s1.[0] < 0x80uy /\ s2.[0] < 0x80uy)
         ; E.lemma_be_to_n_is_bounded s1
         ; E.lemma_be_to_n_is_bounded s2
         ; assert_norm (Int.size (E.be_to_n s1) 32)
         ; assert_norm (Int.size (E.be_to_n s2) 32)
         ; assert_norm (v (u #(Signed W32) (E.be_to_n s1)) == E.be_to_n s1)
         ; assert_norm (v (u #(Signed W32) (E.be_to_n s2)) == E.be_to_n s2)
         ; assert_norm (E.be_to_n s1 == E.be_to_n s2)
         ; E.be_to_n_inj s1 s2 )
#pop-options

/// Prove that the our decoding function is injective
let synth_asn1_integer_injective' l s1 s2
= if s1.[0] = 0x00uy then
  ( synth_asn1_integer_injective_with_leading_zero l s1 s2 )
  else if s2.[0] = 0x00uy then
  ( synth_asn1_integer_injective_with_leading_zero l s2 s1 )
  else
  ( synth_asn1_integer_injective_without_leading_zero l s1 s2 )

let synth_asn1_integer_injective l
= synth_injective_intro'
  (* f *) (synth_asn1_integer l)
  (*prf*) (synth_asn1_integer_injective' l)

///
/// Parser
///
let parse_asn1_integer l
= synth_asn1_integer_injective l;
  parse_seq_flbytes l
  `parse_filter`
  filter_asn1_integer l
  `parse_synth`
  synth_asn1_integer l

///
/// Serializer
///
let serialize_asn1_integer l
= serialize_synth
  (* p1 *) (parse_seq_flbytes l
            `parse_filter`
            filter_asn1_integer l)
  (* f2 *) (synth_asn1_integer l)
  (* s1 *) (serialize_seq_flbytes l
            `serialize_filter`
            filter_asn1_integer l)
  (* g1 *) (synth_asn1_integer_inverse l)
  (* prf*) (synth_asn1_integer_injective l)

///
/// Lemmas
///

/// Reveal the computation of parse
let lemma_parse_asn1_integer_unfold l input
= parse_filter_eq
  (* p *) (parse_seq_flbytes l)
  (* f *) (filter_asn1_integer l)
  (* in*) (input);
  synth_asn1_integer_injective l;
  parse_synth_eq
  (* p *) (parse_seq_flbytes l
           `parse_filter`
           filter_asn1_integer l)
  (* f *) (synth_asn1_integer l)
  (* in*) (input)

/// Reveal the computaion of serialize
let lemma_serialize_asn1_integer_unfold l value
= serialize_filter_correct
  (* p *) (serialize_seq_flbytes l)
  (* f *) (filter_asn1_integer l);
  synth_asn1_integer_injective l;
  serialize_synth_eq
  (* p1 *) (parse_seq_flbytes l
            `parse_filter`
            filter_asn1_integer l)
  (* f2 *) (synth_asn1_integer l)
  (* s1 *) (serialize_seq_flbytes l
            `serialize_filter`
            filter_asn1_integer l)
  (* g1 *) (synth_asn1_integer_inverse l)
  (* prf*) (synth_asn1_integer_injective l)
  (* val*) (value)

/// Reveal the size of a serialization
let lemma_serialize_asn1_integer_size l value
= parser_kind_prop_equiv (parse_asn1_integer_kind l) (parse_asn1_integer l);
  lemma_serialize_asn1_integer_unfold l value


///////////////////////////////////////////////////////////
//// ASN1 aux `INTEGER` TLV Parser and Serializer
///////////////////////////////////////////////////////////

/// parser tag for the `tagged_union` combinators
let parser_tag_of_asn1_integer value
= (INTEGER, u (length_of_asn1_integer value))

///
/// A pair of aux parser/serializer, which explicitly coerce the `INTEGER` value
/// between the subtype used by `INTEGER` value parser/serialzier and `INTEGER`
/// TLV parser/serializer.
///
/// NOTE: I found that have this aux parser explicitly defined will make the prove of
///       `_unfold` lemmas simpler.
///

/// Convert an `INTEGER` value from the subtype used by its value parser to the subtype
/// used by its TLV parser/serializer
/// (value : subtype_{value}) <: subtype_{TLV}
let synth_asn1_integer_V tag value
= value

/// Convert an `INTEGER` value from the subtype used by its TLV parser to the subtype
/// used by its value parser/serializer
/// (value : subtype_{TLV}) <: subtype_{value}
let synth_asn1_integer_V_inverse tag value'
= value'

///
/// Aux parser
///
let parse_asn1_integer_V tag
= (weak_kind_of_type INTEGER
   `weaken`
   parse_asn1_integer (v (snd tag)))
   `parse_synth`
   synth_asn1_integer_V tag

///
/// Aux serializer
///
let serialize_asn1_integer_V tag
= serialize_synth
  (* p1 *) (weak_kind_of_type INTEGER
            `weaken`
            parse_asn1_integer (v (snd tag)))
  (* f2 *) (synth_asn1_integer_V tag)
  (* s1 *) (weak_kind_of_type INTEGER
            `serialize_weaken`
            serialize_asn1_integer (v (snd tag)))
  (* g1 *) (synth_asn1_integer_V_inverse tag)
  (* prf*) ()

///
/// Lemmas
///

/// Reveal the computation of parse
let lemma_parse_asn1_integer_V_unfold tag input
= parse_synth_eq
  (* p1 *) (weak_kind_of_type INTEGER
            `weaken`
            parse_asn1_integer (v (snd tag)))
  (* f2 *) (synth_asn1_integer_V tag)
  (* in *) input

/// Reveal the computation of serialzation
noextract
let lemma_serialize_asn1_integer_V_unfold
  (tag: (the_asn1_tag INTEGER & asn1_value_int32_of_type INTEGER))
  (value: refine_with_tag parser_tag_of_asn1_integer tag)
: Lemma (
  serialize (serialize_asn1_integer_V tag) value ==
  serialize (serialize_asn1_integer (v (snd tag))) value
)
= serialize_synth_eq
  (* p1 *) (weak_kind_of_type INTEGER
            `weaken`
            parse_asn1_integer (v (snd tag)))
  (* f2 *) (synth_asn1_integer_V tag)
  (* s1 *) (weak_kind_of_type INTEGER
            `serialize_weaken`
            serialize_asn1_integer (v (snd tag)))
  (* g1 *) (synth_asn1_integer_V_inverse tag)
  (* prf*) ()
  (* in *) (value)


//////////////////////////////////////////////////////////
///
/// ASN1 `INTEGER` TLV Parser
///
let parse_asn1_integer_TLV
= parse_tagged_union
  (* pt *) (parse_asn1_tag_of_type INTEGER
            `nondep_then`
            parse_asn1_length_of_type INTEGER)
  (* tg *) (parser_tag_of_asn1_integer)
  (* p  *) (parse_asn1_integer_V)

///
/// ASN1 `INTEGER` TLV Serialzier
///
#push-options "--initial_fuel 4"
let serialize_asn1_integer_TLV
= serialize_tagged_union
  (* st *) (serialize_asn1_tag_of_type INTEGER
            `serialize_nondep_then`
            serialize_asn1_length_of_type INTEGER)
  (* tg *) (parser_tag_of_asn1_integer)
  (* s  *) (serialize_asn1_integer_V)
#pop-options

///
/// Lemmas
///

/// Reveal the computation of parse
#restart-solver
#push-options "--z3rlimit 32 --initial_ifuel 8"
let lemma_parse_asn1_integer_TLV_unfold input
= nondep_then_eq
  (* p1 *) (parse_asn1_tag_of_type INTEGER)
  (* p2 *) (parse_asn1_length_of_type INTEGER)
  (* in *) (input);

  let parser_tag = parse (parse_asn1_tag_of_type INTEGER
                          `nondep_then`
                          parse_asn1_length_of_type INTEGER) input in
  if (Some? parser_tag) then
  ( let Some (parser_tag, length) = parser_tag in
    lemma_parse_asn1_integer_V_unfold parser_tag (Seq.slice input length (Seq.length input)) );

  parse_tagged_union_eq
  (* pt *) (parse_asn1_tag_of_type INTEGER
            `nondep_then`
            parse_asn1_length_of_type INTEGER)
  (* tg *) (parser_tag_of_asn1_integer)
  (* p  *) (parse_asn1_integer_V)
  (* in *) (input)
#pop-options

/// Reveal the computation of serialize
#push-options "--z3rlimit 32"
let lemma_serialize_asn1_integer_TLV_unfold value
= serialize_nondep_then_eq
  (* s1 *) (serialize_asn1_tag_of_type INTEGER)
  (* s2 *) (serialize_asn1_length_of_type INTEGER)
  (* in *) (parser_tag_of_asn1_integer value);
  lemma_serialize_asn1_integer_V_unfold (parser_tag_of_asn1_integer value) value;
  serialize_tagged_union_eq
  (* st *) (serialize_asn1_tag_of_type INTEGER
            `serialize_nondep_then`
            serialize_asn1_length_of_type INTEGER)
  (* tg *) (parser_tag_of_asn1_integer)
  (* s  *) (serialize_asn1_integer_V)
  (* in *) (value)
#pop-options

/// Reveal the size of a serialzation
#push-options "--z3rlimit 16"
let lemma_serialize_asn1_integer_TLV_size value
= let length = length_of_asn1_integer value in
  let len: asn1_value_int32_of_type INTEGER = u length in
  lemma_serialize_asn1_integer_TLV_unfold value;
  lemma_serialize_asn1_tag_of_type_size INTEGER INTEGER;
  lemma_serialize_asn1_length_size len;
  serialize_asn1_length_of_type_eq INTEGER len;
  lemma_serialize_asn1_integer_size length value
#pop-options
