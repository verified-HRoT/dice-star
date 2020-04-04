module ASN1.Test

open LowParse.Spec.Base
open LowParse.Spec.Combinators
open LowParse.Spec.List
open LowParse.Spec.Int
open LowParse.Spec.SeqBytes.Base

open FStar.Integers

/// Experiment for runtime length verification
///

let lbytes = Seq.Properties.lseq byte

let tag_of_data
  (s: bytes{Seq.length s <= 255})
: GTot (n: uint_8)
= u (Seq.length s)

let synth_data
  (n: uint_8)
  (s: lbytes (v n))
: GTot (refine_with_tag tag_of_data n)
= s

let synth_data_inverse
  (n: uint_8)
  (x: refine_with_tag tag_of_data n)
: GTot (s: lbytes (v n){ x == synth_data n s })
= x

let parse_data_kind (n: uint_8) = total_constant_size_parser_kind (v n)
let parse_data
  (n: uint_8)
: parser (parse_data_kind n) (refine_with_tag tag_of_data n)
= parse_seq_flbytes (v n)
  `parse_synth`
  synth_data n

let serialize_data
    (n: uint_8)
: serializer (parse_data n)
= serialize_synth
  (* p1 *) (parse_seq_flbytes (v n))
  (* f2 *) (synth_data n)
  (* s1 *) (serialize_seq_flbytes (v n))
  (* g1 *) (synth_data_inverse n)
  (* Prf*) ()

let parse_data_kind_weak = strong_parser_kind 0 255 None
let parse_data_weak
  (n: uint_8)
: parser parse_data_kind_weak (refine_with_tag tag_of_data n)
= parse_data_kind_weak
  `weaken`
  parse_data n

let serialize_data_weak
  (n: uint_8)
: serializer (parse_data_weak n)
= parse_data_kind_weak
  `serialize_weaken`
  serialize_data n

let parse_test
= parse_tagged_union
  (* pt *) (parse_u8)
  (* tg *) (tag_of_data)
  (* p  *) (parse_data_weak)

let serialize_test
: serializer parse_test
= serialize_tagged_union
  (* st *) (serialize_u8)
  (* tg *) (tag_of_data)
  (* s  *) (serialize_data_weak)

open LowParse.Spec.FLData

let test (): Lemma (
  let px = parse (parse_test) (Seq.create 50 1uy) in
  Some? px /\ snd (Some?.v px) == 2 /\ fst (Some?.v px) == Seq.create 1 1uy
)
= let s = (Seq.create 50 1uy) in
  // parser_kind_prop_equiv (get_parser_kind parse_test) parse_test;
  parse_tagged_union_eq
  (* pt *) (parse_u8)
  (* tg *) (tag_of_data)
  (* p  *) (parse_data_weak)
  (* in *) (Seq.create 50 1uy);
  // parse_u8_spec s;
  parser_kind_prop_equiv parse_u8_kind parse_u8;
  let Some (tag, 1) = parse parse_u8 s in
  parse_u8_spec' s;
  assert (tag == 1uy);
  let s' = Seq.slice s 1 (Seq.length s) in
  assert (Seq.index s' 0 == 1uy);
  assert (Seq.length s' == 49);
  Seq.lemma_split s 1;
  Seq.lemma_index_slice s 1 (Seq.length s) 0;
  assert (Seq.index s' 0 == 1uy);
  // Seq.lemma_eq_intro s' (Seq.create 49 1uy);
  assert (s' `Seq.equal` Seq.create 49 1uy);
  parser_kind_prop_equiv (parse_data_kind tag) (parse_data_weak tag);
  parse_synth_eq
  (* p1 *) (parse_seq_flbytes (v tag))
  (* f2 *) (synth_data tag)
  (* in *) (s');
  parser_kind_prop_equiv (get_parser_kind (parse_seq_flbytes (v tag))) (parse_seq_flbytes (v tag));
  let pdata = parse (parse_data tag) s' in
  assert (Some? pdata);
  assert (snd (Some?.v pdata) == 1);
  assert (fst (Some?.v pdata) `Seq.equal` Seq.create 1 1uy);
()

let test2 (): Lemma (
  let px = parse (parse_fldata_strong (serialize_test) 2) (Seq.create 50 1uy) in
  Some? px
)
= let s = (Seq.create 50 1uy) in
  // parser_kind_prop_equiv (get_parser_kind parse_test) parse_test;
  parse_tagged_union_eq
  (* pt *) (parse_u8)
  (* tg *) (tag_of_data)
  (* p  *) (parse_data_weak)
  (* in *) (Seq.create 50 1uy);
  // parse_u8_spec s;
  parser_kind_prop_equiv parse_u8_kind parse_u8;
  let Some (tag, 1) = parse parse_u8 s in
  parse_u8_spec' s;
  assert (tag == 1uy);
  let s' = Seq.slice s 1 (Seq.length s) in
  assert (Seq.index s' 0 == 1uy);
  assert (Seq.length s' == 49);
  Seq.lemma_split s 1;
  Seq.lemma_index_slice s 1 (Seq.length s) 0;
  assert (Seq.index s' 0 == 1uy);
  // Seq.lemma_eq_intro s' (Seq.create 49 1uy);
  assert (s' `Seq.equal` Seq.create 49 1uy);
  parser_kind_prop_equiv (parse_data_kind tag) (parse_data_weak tag);
  parse_synth_eq
  (* p1 *) (parse_seq_flbytes (v tag))
  (* f2 *) (synth_data tag)
  (* in *) (s');
  parser_kind_prop_equiv (get_parser_kind (parse_seq_flbytes (v tag))) (parse_seq_flbytes (v tag));
  let pdata = parse (parse_data tag) s' in
  assert (Some? pdata);
  assert (snd (Some?.v pdata) == 1);
  assert (fst (Some?.v pdata) `Seq.equal` Seq.create 1 1uy);
  let px_ = parse parse_test s in
  assert (px_ == Some (Seq.create 1 1uy, 2));
  let s02 = Seq.slice s 0 2 in
  Seq.lemma_eq_intro s02 (Seq.create 2 1uy);
  assert (s02 == Seq.create 2 1uy);
  let px__ = parse parse_test s02 in
  parse_tagged_union_eq
  (* pt *) (parse_u8)
  (* tg *) (tag_of_data)
  (* p  *) (parse_data_weak)
  (* in *) (s02);
  parse_u8_spec' s02;
  assert (Some? px__);
()

let elim_lem
  (#p: parser 'k 't)
  (s: serializer p)
  (input: bytes)
: Lemma (
  Some? (parse p input) ==> (
    Some? (parse p (Seq.slice input 0 (snd (Some?.v (parse p input)))))
  )
)
= let px = parse p input in
  if Some? px then
  ( let Some (v, l) = px in
    let input' = Seq.slice input 0 l in
    let px' = parse p input' in
    serializer_correct_implies_complete p s;
    assert (Some? px'))
  else
  ( () )

let test2' (): Lemma (
  let px = parse (parse_fldata (parse_test) 2) (Seq.create 50 1uy) in
  Some? px
)
= let s = (Seq.create 50 1uy) in
  assert (Seq.length s >= 2);
  let s02 = Seq.slice s 0 2 in
  Seq.lemma_eq_intro s02 (Seq.create 2 1uy);
  assert (s02 == Seq.create 2 1uy);
  let parse parse_test s02

(* QED *) ()

let parse_test_2 = parse_test `nondep_then` parse_test

let test2 (): Lemma (
  let px = parse (parse_fldata (parse_test) 2) (Seq.create 50 1uy) in
  Some? px
)

let parse_data_weak_length_prop
  (n: uint_8)
  (input: bytes)
: Lemma (
  let px = parse (parse_data n) input in
  let px_weak = parse (parse_data_weak n) input in
  (Some? px ==> snd (Some?.v px_weak) == v n)
)
= parser_kind_prop_equiv (get_parser_kind (parse_data n)) (parse_data n)

let parser_weaken_length_prop
  (input: bytes)
  (#t: Type0)
  (#k: parser_kind)
  (p: parser k t)
  (#k': parser_kind{k' `is_weaker_than` k})
: Lemma (
  let p' = k' `weaken` p in
  let px = parse p input in
  let px' = parse p' input in
  px == px'
)
= ()

let parse_test
= parse_tagged_union
  (* pt *) (parse_u8)
  (* tg *) (tag_of_data)
  (* p  *) (parse_data_weak)

/// TODO: Can we reason about the "runtime" length properties of `parse_test`?
///

let runtime_length_prop
  (s: bytes)
: Lemma (
  parse parse_test s ==
 (match parse parse_u8 s with
  | None -> None
  | Some (tag, consumed_tag) ->
    (let s' = Seq.slice s consumed_tag (Seq.length s) in
     match parse (parse_data tag) s' with
     | None -> None
     | Some (data, consumed_data) -> Some ((data <: s: bytes{Seq.length s <= 255}), (consumed_tag + consumed_data <: consumed_length s))))
)
= parse_tagged_union_eq
  (* pt *) (parse_u8)
  (* tg *) (tag_of_data)
  (* p  *) (parse_data_weak)
  (* in *) (s)


let parse_exact_prop
  (s: bytes)
  (p: parser 'k 't)
: Lemma (
  let px = parse p s in
 (Some? px ==>
 (let Some (v, l) = px in
  let px' = parse (parse_exact p l) s in
  Some? px'
  ))
)= ()

let runtime_exact_length_prop
  (s: bytes)
: Lemma (
  parse parse_test s ==
 (match parse parse_u8 s with
  | None -> None
  | Some (tag, consumed_tag) ->
    (let s' = Seq.slice s consumed_tag (Seq.length s) in
     match parse (parse_exact (parse_data tag) (v tag)) s' with
     | None -> None
     | Some (data, consumed_data) -> Some ((data <: s: bytes{Seq.length s <= 255}), (consumed_tag + consumed_data <: consumed_length s))))
)
= parse_tagged_union_eq
  (* pt *) (parse_u8)
  (* tg *) (tag_of_data)
  (* p  *) (parse_data_weak)
  (* in *) (s)

open LowParse.Spec.FLData

let parse_u8_2 = parse_u8 `nondep_then` parse_u8

let test (): Lemma (
  let px = parse (parse_fldata (parse_u8 `nondep_then` parse_u8) 2) (Seq.create 5 1uy) in
  Some? px
) = parse_u8_spec (Seq.create 5 1uy);
    parser_kind_prop_equiv (get_parser_kind parse_u8) parse_u8;
    // nondep_then_eq parse_u8 parse_u8 (Seq.create 2 1uy);
    parser_kind_prop_equiv (get_parser_kind parse_u8_2) parse_u8_2

(*)
type ty: Type =
| BS
| SQ

type vl: Type =
| BSV: v: list byte -> vl
| SQV: l: list vl -> vl

// let tag_of_data
//   (value: vl)
// : GTot (tag: (byte * byte))
// = match value with
//   | BSV blst -> (0x00uy, I.u (List.length blst))
//   | SQV vlst -> (0xFFuy, I.u (List.length vlst))

let rec parse_v_bare
  (x: byte * byte)
  (b: bytes)
: GTot (options (vl * consumed_length b))

and parse_tv_bare
  (b: bytes)
: GTot (option (vl * consumed_length b))
  (decreases %[(Seq.length b); 0])
= match parse (parse_u8 `nondep_then` parse_u8) b with
  | None -> None
  | Some (x, n) -> ( let tag, len = x in
                     let l = I.v len in
                     if n <= 0 || n + l > Seq.length b || l <= 0 then
                     ( None )
                     else
                     ( let b' = (Seq.slice b n (n+l)) in
                       assert (Seq.length b' < Seq.length b);
                       match tag with
                       | 0x00uy -> (match parse (parse_list parse_u8) b' with
                                    | None -> None
                                    | Some (s, n) -> Some (BSV s, (n <: consumed_length b')))
                       | 0xFFuy -> (match parse_sqv_bare b' with
                                    | None -> None
                                    | Some (lt, n) -> Some (SQV lt, (n <: consumed_length b')))
                       | _       -> None ))

and parse_sqv_bare
  (b: bytes)
: GTot (option (list vl * consumed_length b))
  (decreases %[(Seq.length b); 1])
= if Seq.length b = 0 then
  ( Some ([], (0 <: consumed_length b)) )
  else
  ( match parse_tv_bare b with
    | None -> None
    | Some (_, 0) -> None
    | Some (v, n) -> ( match parse_sqv_bare (Seq.slice b n (Seq.length b)) with
                       | None -> None
                       | Some (l, n') -> Some (v :: l, (n + n' <: consumed_length b))))
