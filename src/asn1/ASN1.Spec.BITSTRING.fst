module ASN1.Spec.BITSTRING

open LowParse.Spec.Base
open LowParse.Spec.Combinators
open LowParse.Spec.SeqBytes.Base

open ASN1.Base
open ASN1.Spec.Tag
open ASN1.Spec.Length

open FStar.Integers

/// TEST
///

// let bs_0: datatype_of_asn1_type BIT_STRING = (|0, Seq.empty|)
// let bs_1: datatype_of_asn1_type BIT_STRING = (|1, Seq.create 1 128uy|)
// let bs_2: datatype_of_asn1_type BIT_STRING = (|2, Seq.create 1 64uy|)
// let bs_3: datatype_of_asn1_type BIT_STRING = (|3, Seq.create 1 32uy|)
// let bs_4: datatype_of_asn1_type BIT_STRING = (|4, Seq.create 1 16uy|)
// let bs_5: datatype_of_asn1_type BIT_STRING = (|5, Seq.create 1 8uy|)
// let bs_6: datatype_of_asn1_type BIT_STRING = (|6, Seq.create 1 4uy|)
// let bs_7: datatype_of_asn1_type BIT_STRING = (|7, Seq.create 1 2uy|)
// let bs_8: datatype_of_asn1_type BIT_STRING = (|8, Seq.create 1 1uy|)
// let bs_9: datatype_of_asn1_type BIT_STRING = (|9, Seq.create 2 128uy|)

(*
   Len = 1, unused = 0, bytes = []
   Len = 2, unused = x, bytes = [_]
*)

let filter_asn1_bit_string
  (l: asn1_length_of_type BIT_STRING)
  (ls: lbytes l)
: GTot (bool)
= let unused_bits = ls.[0] in
  if l = 1 then
  ( unused_bits = 0uy )
  else
  ( let mask = normalize_term (pow2 (v unused_bits)) in
    unused_bits <= 7uy && 0 = normalize_term ((v ls.[l - 1]) % mask) )

let synth_asn1_bit_string
  (l: asn1_length_of_type BIT_STRING)
  (ls: parse_filter_refine (filter_asn1_bit_string l))
: GTot (x: datatype_of_asn1_type BIT_STRING {
           let (|bits, s|) = x in
           let bytes_length = normalize_term ((bits + 7) / 8) in
           let unused_bits = normalize_term ((bytes_length * 8) - bits) in
           v ls.[0] == unused_bits /\
           l == bytes_length + 1 })
= let unused_bits = ls.[0] in
  let s = Seq.slice ls 1 l in
  if l = 1 then
  ( assert_norm ( v unused_bits == 0 )
  ; let bits: n:nat{n == 0} = normalize_term ((l - 1) * 8 - (v unused_bits)) in
    (|bits, s|) )
  else
  ( assert_norm ( v unused_bits <= 7 )
  ; let bits: n:nat {
        0 <= n /\
        n <= normalize_term ((asn1_length_max - 1) * 8)
    } = normalize_term ((l - 1) * 8 - (v unused_bits)) in
    (|bits, s|) )

#push-options "--query_stats --z3rlimit 16"
let synth_asn1_bit_string_injective'
  (l: asn1_length_of_type BIT_STRING)
  (ls1 ls2: parse_filter_refine (filter_asn1_bit_string l))
: Lemma
  (requires synth_asn1_bit_string l ls1 == synth_asn1_bit_string l ls2)
  (ensures ls1 `Seq.equal` ls2)
=
  let unused_bits1 = ls1.[0] in
  let unused_bits2 = ls2.[0] in
  let s1 = Seq.slice ls1 1 l in
  let s2 = Seq.slice ls2 1 l in
  assert_norm ((unused_bits1 `Seq.cons` s1) `Seq.equal` ls1);
  assert_norm ((unused_bits2 `Seq.cons` s2) `Seq.equal` ls2);
  if l = 1 then
  ( assert_norm (unused_bits1 == unused_bits2) )
  else
  ( let bits1: n:nat {
        0 <= n /\
        n <= normalize_term ((asn1_length_max - 1) * 8)
    } = normalize_term ((l - 1) * 8 - (v unused_bits1)) in
    let bits2: n:nat {
        0 <= n /\
        n <= normalize_term ((asn1_length_max - 1) * 8)
    } = normalize_term ((l - 1) * 8 - (v unused_bits2)) in
    assert_norm (bits1 == bits2)
  ; assert_norm (unused_bits1 == unused_bits2)
  ; assert_norm (s1 `Seq.equal` s2)
  ; assert_norm ((unused_bits1 `Seq.cons` s1) `Seq.equal` ls1)
  ; assert_norm ((unused_bits2 `Seq.cons` s2) `Seq.equal` ls2) )
#pop-options

let synth_asn1_bit_string_injective
  (l: asn1_length_of_type BIT_STRING)
: Lemma (
  synth_injective (synth_asn1_bit_string l)
)
= synth_injective_intro' (synth_asn1_bit_string l) (synth_asn1_bit_string_injective' l)

let synth_asn1_bit_string_inverse
  (l: asn1_length_of_type BIT_STRING)
  (x: datatype_of_asn1_type BIT_STRING {
           let (|bits, s|) = x in
           let bytes_length = normalize_term ((bits + 7) / 8) in
           let unused_bits = normalize_term ((bytes_length * 8) - bits) in
           l == bytes_length + 1 })
: GTot (ls: parse_filter_refine (filter_asn1_bit_string l) { x == synth_asn1_bit_string l ls })
= let (|bits, s|) = x in
  let bytes_length: l:asn1_length_t { l <= asn1_length_max - 1 } = l - 1 in
  let unused_bits: n:nat{0 <= n /\ n <= 7} = normalize_term ((bytes_length * 8) - bits) in
  assert (Seq.length s == bytes_length);
  let ls: parse_filter_refine (filter_asn1_bit_string l)
      = normalize_term (Seq.create 1 (u unused_bits) `Seq.append` s) in
  assert_norm (bytes_length == 0 ==>
                 unused_bits == 0);
  assert_norm (bytes_length <> 0 ==>
                 unused_bits <= 7 /\
                (bytes_length * 8 - unused_bits == bits));
  assert (Seq.slice ls 1 l `Seq.equal` s);
  assert (x == synth_asn1_bit_string l ls);
  ls

let parse_asn1_bit_string
  (l: asn1_length_of_type BIT_STRING)
: parser _ (x: datatype_of_asn1_type BIT_STRING {
               let (|bits, s|) = x in
               let bytes_length = normalize_term ((bits + 7) / 8) in
               let unused_bits = normalize_term ((bytes_length * 8) - bits) in
               l == bytes_length + 1 })
= synth_asn1_bit_string_injective l;
  parse_seq_flbytes l
  `parse_filter`
  filter_asn1_bit_string l
  `parse_synth`
  synth_asn1_bit_string l

#push-options "--query_stats --z3rlimit 16 --lax"
let parse_asn1_bit_string_unfold
  (l: asn1_length_of_type BIT_STRING)
  (input: bytes)
: Lemma (
  parse (parse_asn1_bit_string l) input ==
 (match parse (parse_seq_flbytes l) input with
  | None -> None
  | Some (ls, consumed) -> ( if filter_asn1_bit_string l ls then
                             ( Some (synth_asn1_bit_string l ls, consumed) )
                             else
                             ( None )))
)
= parse_filter_eq
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
#pop-options

let serialize_asn1_bit_string
  (l: asn1_length_of_type BIT_STRING)
: serializer (parse_asn1_bit_string l)
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

let parser_tag_of_bit_string
  (x: datatype_of_asn1_type BIT_STRING)
: GTot (the_asn1_type BIT_STRING & asn1_int32_of_type BIT_STRING)
= let (|bits, s|) = x in
  let bytes_length = normalize_term ((bits + 7) / 8) in
  let len: asn1_int32_of_type BIT_STRING = u (bytes_length + 1) in
  (BIT_STRING, len)

let synth_asn1_bit_string_TLV
  (tag: (the_asn1_type BIT_STRING & asn1_int32_of_type BIT_STRING))
  (value: datatype_of_asn1_type BIT_STRING {
          let (|bits, s|) = value in
          let bytes_length = normalize_term ((bits + 7) / 8) in
          let unused_bits = normalize_term ((bytes_length * 8) - bits) in
          v (snd tag) == bytes_length + 1 })
: GTot (value': refine_with_tag parser_tag_of_bit_string tag)
= value

let synth_asn1_bit_string_TLV_inverse
  (tag: (the_asn1_type BIT_STRING & asn1_int32_of_type BIT_STRING))
  (value': refine_with_tag parser_tag_of_bit_string tag)
: GTot (value: datatype_of_asn1_type BIT_STRING {
               let (|bits, s|) = value in
               let bytes_length = normalize_term ((bits + 7) / 8) in
               let unused_bits = normalize_term ((bytes_length * 8) - bits) in
               v (snd tag) == bytes_length + 1 /\
               value' == synth_asn1_bit_string_TLV tag value})
= value'

let parse_asn1_bit_string_TLV
= parse_tagged_union
  (* pt *) (parse_the_asn1_tag BIT_STRING
            `nondep_then`
            parse_asn1_length_of_type BIT_STRING)
  (* tg *) (parser_tag_of_bit_string)
  (* p  *) (fun parser_tag -> weak_kind_of_type BIT_STRING
                            `weaken`
                           (parse_asn1_bit_string (v (snd parser_tag))
                            `parse_synth`
                            synth_asn1_bit_string_TLV parser_tag))

#push-options "--query_stats --initial_fuel 4"
let serialize_asn1_bit_string_TLV
: serializer parse_asn1_bit_string_TLV
= serialize_tagged_union
  (* st *) (serialize_the_asn1_tag BIT_STRING
            `serialize_nondep_then`
            serialize_asn1_length_of_type BIT_STRING)
  (* tg *) (parser_tag_of_bit_string)
  (* s  *) (fun parser_tag -> weak_kind_of_type BIT_STRING
                            `serialize_weaken`
                           (serialize_synth
                            (* p1 *) (parse_asn1_bit_string (v (snd parser_tag)))
                            (* f2 *) (synth_asn1_bit_string_TLV parser_tag)
                            (* s1 *) (serialize_asn1_bit_string (v (snd parser_tag)))
                            (* g1 *) (synth_asn1_bit_string_TLV_inverse parser_tag)
                            (* prf*) ()))
#pop-options
