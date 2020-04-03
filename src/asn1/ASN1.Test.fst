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
  (s: lbytes (v n))
: GTot (refine_with_tag tag_of_data n)

let parse_data
  (n: uint_8)
: parser _ (refine_with_tag tag_of_data n)
= parse_seq_flbytes (v n)
  `parse_synth`
  synth_data n

let parse_data_kind_weak = strong_parser_kind 0 255 None
let parse_data_weak
  (n: uint_8)
: parser parse_data_kind_weak (refine_with_tag tag_of_data n)
= parse_data_kind_weak
  `weaken`
  parse_data n

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
