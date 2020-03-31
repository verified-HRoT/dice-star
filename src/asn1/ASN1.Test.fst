module ASN1.Test

open LowParse.Spec.Base
open LowParse.Spec.Combinators
open LowParse.Spec.List
open LowParse.Spec.Int

module I = FStar.Integers

type ty =
| BS
| SQ

type vl =
| BSV: v: list byte -> vl
| SQV: l: list vl -> vl

val foo : l:list int -> Tot int (decreases %[l;0])
val bar : l:list int -> Tot int (decreases %[l;1])
let rec foo l = match l with
    | [] -> 0
    | x :: xs -> bar xs
and bar l = foo l



let rec parse_tv_bare
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
                       | 0x0uy -> (match (parse_list_bare parse_u8) b' with
                                   | None -> None
                                   | Some (s, n) -> Some (BSV s, (n <: consumed_length b')))
                       | _     -> (match parse_sqv_bare b' with
                                   | None -> None
                                   | Some (lt, n) -> Some (SQV lt, (n <: consumed_length b')))) )

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
