module ASN1.Spec.BIT_STRING

open LowParse.Spec.Base
open LowParse.Spec.Combinators
open LowParse.Spec.SeqBytes.Base

open ASN1.Base
open ASN1.Spec.Tag
open ASN1.Spec.Length

open FStar.Integers

module B32 = FStar.Bytes

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

let filter_asn1_bit_string
  (l: asn1_length_of_type BIT_STRING)
  (raw: lbytes l)
: GTot (bool)
= let unused_bits = raw.[0] in
  if l = 1 then
  ( unused_bits = 0uy )
  else
  ( let mask = normalize_term (pow2 (v unused_bits)) in
    0uy <= unused_bits && unused_bits <= 7uy &&
    0 = normalize_term ((v raw.[l - 1]) % mask) )

let synth_asn1_bit_string
  (l: asn1_length_of_type BIT_STRING)
  (raw: parse_filter_refine (filter_asn1_bit_string l))
: GTot (value: datatype_of_asn1_type BIT_STRING {
               let (|len, unused_bits, s|) = value in
               l == v len })
= let unused_bits: n: asn1_int32 {0 <= v n /\ v n <= 7} = cast raw.[0] in
  let s32 = B32.hide (Seq.slice raw 1 l) in
  (|u l, unused_bits, s32|)

// let unused_bits = ls.[0] in
//   let s = Seq.slice ls 1 l in
//   if l = 1 then
//   ( assert_norm ( v unused_bits == 0 )
//   ; let bits: n:uint_32{v n == 0} = normalize_term (u ((l - 1) * 8 - (v unused_bits))) in
//     (|bits, s|) )
//   else
//   ( assert_norm ( v unused_bits <= 7 )
//   ; let bits: n:uint_32 {
//         0 <= v n /\
//         v n <= normalize_term (u ((asn1_length_max - 1) * 8))
//     } = normalize_term (u ((l - 1) * 8 - (v unused_bits))) in
//     (|bits, s|) )

#push-options "--query_stats --z3rlimit 16"
let synth_asn1_bit_string_injective'
  (l: asn1_length_of_type BIT_STRING)
  (raw1 raw2: parse_filter_refine (filter_asn1_bit_string l))
: Lemma
  (requires synth_asn1_bit_string l raw1 == synth_asn1_bit_string l raw2)
  (ensures raw1 == raw2)
= Seq.lemma_split raw1 1;
  Seq.lemma_split raw2 1;
  assert (raw1 `Seq.equal` raw2)
  // let unused_bits1 = raw1.[0] in
  // let unused_bits2 = raw2.[0] in
  // let s1 = Seq.slice raw1 1 l in
  // let s2 = Seq.slice raw2 1 l in
  // assert ( unused_bits1 == unused_bits2 /\
  //          s1 `Seq.equal` s2 /\
  //          (unused_bits1 `Seq.cons` s1) `Seq.equal` raw1 /\
  //          (unused_bits2 `Seq.cons` s2) `Seq.equal` raw2 );
  // assert_norm ((unused_bits1 `Seq.cons` s1) `Seq.equal` raw1);
  // assert_norm ((unused_bits2 `Seq.cons` s2) `Seq.equal` raw2);
  // if l = 1 then
  // ( assert_norm (unused_bits1 == unused_bits2) )

  // ( let bits1: n:nat {
  //       0 <= n /\
  //       n <= normalize_term ((asn1_length_max - 1) * 8)
  //   } = normalize_term ((l - 1) * 8 - (v unused_bits1)) in
  //   let bits2: n:nat {
  //       0 <= n /\
  //       n <= normalize_term ((asn1_length_max - 1) * 8)
  //   } = normalize_term ((l - 1) * 8 - (v unused_bits2)) in
  //   assert_norm (bits1 == bits2)
  // ; assert_norm (unused_bits1 == unused_bits2)
  // ; assert_norm (s1 `Seq.equal` s2)
  // ; assert_norm ((unused_bits1 `Seq.cons` s1) `Seq.equal` raw1)
  // ; assert_norm ((unused_bits2 `Seq.cons` s2) `Seq.equal` raw2) )
#pop-options

let synth_asn1_bit_string_injective
  (l: asn1_length_of_type BIT_STRING)
: Lemma (
  synth_injective (synth_asn1_bit_string l)
)
= synth_injective_intro'
  (* f *) (synth_asn1_bit_string l)
  (*prf*) (synth_asn1_bit_string_injective' l)

let synth_asn1_bit_string_inverse
  (l: asn1_length_of_type BIT_STRING)
  (value: datatype_of_asn1_type BIT_STRING {
          let (|len, unused_bits, s|) = value in
          l == v len })
: GTot (raw: parse_filter_refine (filter_asn1_bit_string l) { value == synth_asn1_bit_string l raw })
= let (|len, unused_bits, s32|) = value in
  let raw = cast unused_bits `Seq.cons` B32.reveal s32 in
  let (|len', unused_bits', s32'|) = synth_asn1_bit_string l raw in
  B32.extensionality s32 s32';
  raw

let parse_asn1_bit_string_kind (l: asn1_length_of_type BIT_STRING) = constant_size_parser_kind l
let parse_asn1_bit_string
  (l: asn1_length_of_type BIT_STRING)
: parser (parse_asn1_bit_string_kind l)
         (value: datatype_of_asn1_type BIT_STRING {
                 let (|len, unused_bits, s|) = value in
                 l == v len })
= synth_asn1_bit_string_injective l;
  parse_seq_flbytes l
  `parse_filter`
  filter_asn1_bit_string l
  `parse_synth`
  synth_asn1_bit_string l

let parse_asn1_bit_string_unfold
  (l: asn1_length_of_type BIT_STRING)
  (input: bytes)
: Lemma (
  parse (parse_asn1_bit_string l) input ==
 (match parse (parse_seq_flbytes l) input with
  | None -> None
  | Some (raw, consumed) -> ( if filter_asn1_bit_string l raw then
                              ( Some (synth_asn1_bit_string l raw, consumed) )
                              else
                              ( None )) )
)
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

let serialize_asn1_bit_string_unfold
  (l: asn1_length_of_type BIT_STRING)
  (value: datatype_of_asn1_type BIT_STRING {
                 let (|len, unused_bits, s|) = value in
                 l == v len })
: Lemma (
  serialize (serialize_asn1_bit_string l) value ==
  serialize (serialize_seq_flbytes l) (synth_asn1_bit_string_inverse l value))
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


////////// TLV //////////
let parser_tag_of_bit_string
  (x: datatype_of_asn1_type BIT_STRING)
: GTot (the_asn1_type BIT_STRING & asn1_int32_of_type BIT_STRING)
= let (|len, unused_bits, s32|) = x in
  (BIT_STRING, len)

let synth_asn1_bit_string_TLV
  (tag: (the_asn1_type BIT_STRING & asn1_int32_of_type BIT_STRING))
  (value: datatype_of_asn1_type BIT_STRING {
                 let (|len, unused_bits, s|) = value in
                 v (snd tag) == v len })
: GTot (value': refine_with_tag parser_tag_of_bit_string tag)
= value

let synth_asn1_bit_string_TLV_inverse
  (tag: (the_asn1_type BIT_STRING & asn1_int32_of_type BIT_STRING))
  (value': refine_with_tag parser_tag_of_bit_string tag)
: GTot (value: datatype_of_asn1_type BIT_STRING {
                 let (|len, unused_bits, s|) = value in
                 v (snd tag) == v len /\
                 value' == synth_asn1_bit_string_TLV tag value})
= value'

let parse_asn1_bit_string_TLV_kind
: parser_kind
= parse_asn1_tag_kind
  `and_then_kind`
  parse_asn1_length_kind_of_type BIT_STRING
  `and_then_kind`
  weak_kind_of_type BIT_STRING

let parse_asn1_bit_string_TLV
: parser parse_asn1_bit_string_TLV_kind (datatype_of_asn1_type BIT_STRING)
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

#push-options "--query_stats --z3rlimit 32"
let parse_asn1_bit_string_TLV_unfold
  (input: bytes)
: Lemma (
  parse parse_asn1_bit_string_TLV input ==
 (match parse (parse_the_asn1_tag BIT_STRING) input with
  | None -> None
  | Some (tag, consumed_tag) ->
    (let input_LV = Seq.slice input consumed_tag (Seq.length input) in
     match parse (parse_asn1_length_of_type BIT_STRING) input_LV with
     | None -> None
     | Some (len, consumed_len) ->
       (let input_V = Seq.slice input_LV consumed_len (Seq.length input_LV) in
        match parse (parse_asn1_bit_string (v len)) input_V with
        | None -> None
        | Some (value, consumed_value) ->
               Some ((synth_asn1_bit_string_TLV (tag, len) value),
                     (consumed_tag + consumed_len + consumed_value <: consumed_length input)))))
)
= parser_kind_prop_equiv (get_parser_kind (parse_the_asn1_tag BIT_STRING)) (parse_the_asn1_tag BIT_STRING);
  parser_kind_prop_equiv (get_parser_kind (parse_asn1_length_of_type BIT_STRING)) (parse_asn1_length_of_type BIT_STRING);

  nondep_then_eq
  (* p1 *) (parse_the_asn1_tag BIT_STRING)
  (* p2 *) (parse_asn1_length_of_type BIT_STRING)
  (* in *) (input);

  let parser_tag = (parse_the_asn1_tag BIT_STRING
                    `nondep_then`
                    parse_asn1_length_of_type BIT_STRING) input in
  if Some? parser_tag then
  ( let Some (parser_tag, length) = parser_tag in
    parser_kind_prop_equiv (get_parser_kind (parse_asn1_bit_string length)) (parse_asn1_bit_string length);
    parse_synth_eq
    (* p *) (parse_asn1_bit_string (v (snd parser_tag)))
    (* f *) (synth_asn1_bit_string_TLV parser_tag)
    (* in*) (Seq.slice input length (Seq.length input)) );

  parse_tagged_union_eq
  (* pt *) (parse_the_asn1_tag BIT_STRING
            `nondep_then`
            parse_asn1_length_of_type BIT_STRING)
  (* tg *) (parser_tag_of_bit_string)
  (* p  *) (fun parser_tag -> weak_kind_of_type BIT_STRING
                            `weaken`
                           (parse_asn1_bit_string (v (snd parser_tag))
                            `parse_synth`
                            synth_asn1_bit_string_TLV parser_tag))
  (* in *) (input);

(*FIXME:*) admit()
#pop-options

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

(*)
#push-options "--query_stats --z3rlimit 32"
let serialize_asn1_bit_string_TLV_unfold
  (value: datatype_of_asn1_type BIT_STRING)
: Lemma (
  serialize serialize_asn1_bit_string_TLV value ==
  serialize (serialize_the_asn1_tag BIT_STRING) BIT_STRING
  `Seq.append`
  serialize (serialize_asn1_length_of_type BIT_STRING) (dfst value)
  `Seq.append`
  serialize (serialize_asn1_bit_string (v (dfst value))) value
)
= serialize_nondep_then_eq
  (* s1 *) (serialize_the_asn1_tag BIT_STRING)
  (* s2 *) (serialize_asn1_length_of_type BIT_STRING)
  (* in *) (parser_tag_of_bit_string value);
  serialize_asn1_bit_string_unfold (parser_tag_of_bit_string value) value;
  serialize_tagged_union_eq
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
  (* in *) (value)
#pop-options

