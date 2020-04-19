module ASN1.Spec.INTEGER

open LowParse.Spec.Base
open LowParse.Spec.Combinators
open LowParse.Spec.Int

open ASN1.Base

(* INTEGER *)
(* 1) Positive: (Leading 0x00uy ++) content
   2) Negative: b[0] & 0x80uy != 0 *)
open LowParse.Spec.Int32le
module E = FStar.Endianness
open FStar.Integers

(*
NOTE: 1. Negative: `**p & 0x80 == 0`, reject
      2. Zero    : as `[0x02; 0x01; 0x00]` for INTEGER or `[0x0A; 0x01; 0x00]` fir ENUMERATED tags
      3. Positive: if the most significant bit of a positive integer is `1`, then add a leading zero.

NOTE: MbedTLS's implementation seems allow arbitrary leading zeros. We only allow one leading zero for now.
NOTE: We only allow at most 4-byte positive integers. If an integer is encoded into 5 bytes with a leading
      zero, then it must be a negative integer.
*)

(*
NOTE: 1. At most one leading zero
      3. after skip leading zero, s.[0] & 0x80 == 0
      0 - 0x7FFFFFFF
*)

let filter_asn1_integer
  (l: asn1_length_of_type INTEGER) (* 1 <= l <= 4*)
  (s: lbytes l)
: GTot (bool)
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

// if s.[0] = 0x00uy then (* has a leading zero *)
//   ( l = 1                 (* is zero *)
//   || (s.[1] >= 0x80uy) )  (* or the next byte's most significant bit is `1` *)
//   else                    (* no leading zero *)
//   ( s.[0] < 0x80uy )     (* the most significant bit is `0` *)

// val lemma_le_to_n_is_bounded_pos: b:bytes -> Lemma
//   (requires True)
//   (ensures  (le_to_n b < pow2 (8 * Seq.length b)))
//   (decreases (Seq.length b))

// let rec lemma_be_to_n_is_bounded b =
//   if Seq.length b = 0 then ()
//   else
//     begin
//     let s = Seq.slice b 0 (Seq.length b - 1) in
//     assert(Seq.length s = Seq.length b - 1);
//     lemma_be_to_n_is_bounded s;
//     assert(UInt8.v (Seq.last b) < pow2 8);
//     assert(be_to_n s < pow2 (8 * Seq.length s));
//     assert(be_to_n b < pow2 8 + pow2 8 * pow2 (8 * (Seq.length b - 1)));
//     lemma_euclidean_division (UInt8.v (Seq.last b)) (be_to_n s) (pow2 8);
//     assert(be_to_n b <= pow2 8 * (be_to_n s + 1));
//     assert(be_to_n b <= pow2 8 * pow2 (8 * (Seq.length b - 1)));
//     Math.Lemmas.pow2_plus 8 (8 * (Seq.length b - 1));
//     lemma_factorise 8 (Seq.length b - 1)
//     end

let length_of_asn1_integer
  (value: datatype_of_asn1_type INTEGER)
: GTot (l: asn1_length_of_type INTEGER)
= let vx = v #(Signed W32) value in
  if      0         <= vx && vx <= 0x7F      then
  ( 1 )
  else if 0x7F       < vx && vx <= 0xFF       then
  ( 2 )
  else if 0xFF       < vx && vx <= 0x7FFF     then
  ( 2 )
  else if 0x7FFF     < vx && vx <= 0xFFFF     then
  ( 3 )
  else if 0xFFFF     < vx && vx <= 0x7FFFFF   then
  ( 3 )
  else if 0x7FFFFF   < vx && vx <= 0xFFFFFF   then
  ( 4 )
  else if 0xFFFFFF   < vx && vx <= 0x7FFFFFFF then
  ( 4 )


(* NOTE: Why ... `unfold` ... *)
#restart-solver
#push-options "--query_stats --z3rlimit 128"
let synth_asn1_integer
  (l: asn1_length_of_type INTEGER)
  (s: parse_filter_refine (filter_asn1_integer l))
: GTot (value: datatype_of_asn1_type INTEGER { l == length_of_asn1_integer value })
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

// if l = 1 then
//   ( E.lemma_be_to_n_is_bounded s
//   ; E.reveal_be_to_n s
//   ; u #(Signed W32) (E.be_to_n s) )
//   else if s.[0] = 0x00uy then
//   ( let s = Seq.slice s 1 l in
//     E.lemma_be_to_n_is_bounded s
//   ; assert_norm(Int.size (E.be_to_n s) 32)
//   ; u #(Signed W32) (E.be_to_n s) )
//   else
//   ( assert_norm (2 <= l /\ l <= 4 /\ s.[0] < 0x80uy)
//   ; E.lemma_be_to_n_is_bounded s
//   ; E.reveal_be_to_n s
//   ; if l = 4 then
//     ( E.reveal_be_to_n (Seq.slice s 0 3) )
//   ; if l >= 3 then
//     ( E.reveal_be_to_n (Seq.slice s 0 2) )
//   ; E.reveal_be_to_n (Seq.slice s 0 1)
//   ; assert_norm (Int.size (E.be_to_n s) 32)
//   ; u #(Signed W32) (E.be_to_n s) )
#pop-options

#push-options "--query_stats --z3rlimit 128 --max_fuel 0 --max_ifuel 0"
let synth_asn1_integer_inverse
  (l: asn1_length_of_type INTEGER)
  (value: datatype_of_asn1_type INTEGER { l == length_of_asn1_integer value } )
: GTot (s: parse_filter_refine (filter_asn1_integer l) { value == synth_asn1_integer l s })
= let vx = v #(Signed W32) value in

  (* 1-byte integer with the most-significant bit `0` *)
  if      (0         <= vx && vx <= 0x7F      ) then
  ( assert_norm (vx < pow2 (8 * 1 - 1) /\
                 vx < pow2 (8 * 1))
  ; let s = n_to_be 1 vx in
    E.reveal_be_to_n s
  ; s )

  (* 1-byte integer with the most-significant bit `1` *)
  else if (0x7F       < vx && vx <= 0xFF      ) then
  ( assert_norm (vx < pow2 (8 * 1))
  ; let s = n_to_be 1 vx in
    E.reveal_be_to_n s
  ; let s = 0x00uy `Seq.cons` s in
    (* NOTE: Seems the relation between `l` and `value` is not strong
             enough, we need to manually prove things here. *)
    E.lemma_be_to_n_is_bounded (Seq.slice s 1 2)
  ; E.reveal_be_to_n (Seq.slice s 1 2)
  ; assert_norm (Int.size (E.be_to_n (Seq.slice s 1 2)) 32)
  ; assert_norm (synth_asn1_integer l s == value)
  ; s )

  (* 2-byte integer with the most-significant bit `0` *)
  else if (0xFF       < vx && vx <= 0x7FFF    ) then
  ( assert_norm (vx < pow2 (8 * 2 - 1) /\
                 vx < pow2 (8 * 2))
  ; let s = n_to_be 2 vx in
    E.reveal_be_to_n s
  ; E.reveal_be_to_n (Seq.slice s 0 1)
  ; s )

  (* 2-byte integer with the most-significant bit `1` *)
  else if (0x7FFF     < vx && vx <= 0xFFFF    ) then
  ( assert_norm (vx < pow2 (8 * 2))
  ; let s = n_to_be 2 vx in
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
  ; let s = n_to_be 3 vx in (* opt *)
    E.reveal_be_to_n s
  ; E.reveal_be_to_n (Seq.slice s 0 2)
  ; E.reveal_be_to_n (Seq.slice s 0 1)
  ; s )

  (* 3-byte integer with the most-significant bit `1` *)
  else if (0x7FFFFF   < vx && vx <= 0xFFFFFF  ) then
  ( assert_norm (vx < pow2 (8 * 3))
  ; let s = n_to_be 3 vx in
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
  ; let s = n_to_be 4 vx in
    E.reveal_be_to_n s
  ; E.reveal_be_to_n (Seq.slice s 0 3)
  ; E.reveal_be_to_n (Seq.slice s 0 2)
  ; E.reveal_be_to_n (Seq.slice s 0 1)
  ; s )

  (* Out of the range of positive 32-bit integer [0, 0x7FFFFFFF], unreachable *)
  else
  ( false_elim () )
#pop-options

open FStar.Tactics

let filter_asn1_integer_prop_leading_zero
  (l: asn1_length_of_type INTEGER)
  (s: parse_filter_refine (filter_asn1_integer l))
: Lemma
  (requires s.[0] == 0x00uy)
  (ensures l == 1 \/ s.[1] >= 0x80uy)
= ()

let filter_asn1_integer_prop_non_leading_zero
  (l: asn1_length_of_type INTEGER)
  (s: parse_filter_refine (filter_asn1_integer l))
: Lemma
  (requires s.[0] <> 0x00uy)
  (ensures s.[0] < 0x80uy)
= ()

#push-options "--query_stats"
let testl
  (l: asn1_length_of_type INTEGER)
  (s: parse_filter_refine (filter_asn1_integer l))
: Lemma
  (requires 0x7Fl < synth_asn1_integer l s /\
                    synth_asn1_integer l s <= 0xFFl)
  (ensures s.[0] == 0x00uy)
= assert (l == 2);
  if s.[0] <> 0x00uy then
  ( assert_norm (s.[0] < 0x80uy)
  ; E.lemma_be_to_n_is_bounded s
  ; E.reveal_be_to_n s
  ; E.reveal_be_to_n (Seq.slice s 0 1)
  ; assert_norm (Int.size (E.be_to_n s) 32)
  ; let value = u #(Signed W32) (E.be_to_n s) in
    assert (value == synth_asn1_integer l s)
  ; let value = synth_asn1_integer l s in
    assert_norm (value > 0xFFl)
  ; false_elim () )
  else
  ( () )
#pop-options

#push-options "--query_stats --z3rlimit 128"
let synth_asn1_integer_injective_with_leading_zero
  (l: asn1_length_of_type INTEGER)
  (s1 s2: parse_filter_refine (filter_asn1_integer l))
: Lemma
  (requires synth_asn1_integer l s1 == synth_asn1_integer l s2 /\
            s1.[0] == 0x00uy)
  (ensures  s2.[0] == 0x00uy /\ s1 `Seq.equal` s2)
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

#push-options "--query_stats --z3rlimit 128"
let synth_asn1_integer_injective_without_leading_zero
  (l: asn1_length_of_type INTEGER)
  (s1 s2: parse_filter_refine (filter_asn1_integer l))
: Lemma
  (requires synth_asn1_integer l s1 == synth_asn1_integer l s2 /\
            s1.[0] <> 0x00uy /\ s2.[0] <> 0x00uy)
  (ensures  s1 `Seq.equal` s2)
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

#push-options "--query_stats"
let synth_asn1_integer_injective'
  (l: asn1_length_of_type INTEGER)
  (s1 s2: parse_filter_refine (filter_asn1_integer l))
: Lemma
  (requires synth_asn1_integer l s1 == synth_asn1_integer l s2)
  (ensures s1 `Seq.equal` s2)
= if s1.[0] = 0x00uy then
  ( synth_asn1_integer_injective_with_leading_zero l s1 s2 )
  else if s2.[0] = 0x00uy then
  ( synth_asn1_integer_injective_with_leading_zero l s2 s1 )
  else
  ( synth_asn1_integer_injective_without_leading_zero l s1 s2 )
#pop-options


(* NOTE: Big Endian *)
(*)
let synth_asn1_integer
  (l: asn1_length_t{l == 4 \/ l == 5})
  (s: bytes{Seq.length s == l})
: GTot (asn1_int32)
= match l,  s.[0], s.[0] / 0x80uy, s.[1] / 0x80uy with
  |     5, 0x00uy,              _,         0x01uy ->
  |     4,      _,         0x00uy,              _ -> decode_int32le

let encode_asn1_integer
  (x: uint_32{ 0 < v x } )
: Tot (bs: bytes{be_to_n bs == v x})
  // 1 <= Seq.length bs /\ Seq.length bs <= 5 /\
  // (U8.v bs.[0]) <= 0x7F /\
  // (bs.[0] == 0x00uy ==> 2 <= Seq.length bs /\ (U8.v bs.[1]) > 0x7F)})
= let vx = v x in
  let bs: bs:bytes{be_to_n bs == vx} =
    if      (0          < vx && vx <= 0xFF      ) then
    ( assert_norm (vx < pow2 (8 * 1))
    ; n_to_be 1 vx )
    else if (0xFF       < vx && vx <= 0xFFFF    ) then
    ( assert_norm (vx < pow2 (8 * 2))
    ; n_to_be 2 vx )
    else if (0xFFFF     < vx && vx <= 0xFFFFFF  ) then
    ( assert_norm (vx < pow2 (8 * 3))
    ; n_to_be 3 vx )
    else if (0xFFFFFF   < vx && vx <= 0xFFFFFFFF) then
    ( assert_norm (vx < pow2 (8 * 4))
    ; n_to_be 4 vx )
    else
    ( fase_elim () ) in
  if ((v bs.[0]) <= 0x7F) then
  ( assert (bs.[0] =!= 0x00uy)
  ; bs )
  else
  ( 0x00uy `Seq.cons` bs )

let lemma_e
  (x: uint_32{ 0 < v x } )
():Lemma (
  forall x.
    let b = encode_asn1_integer x in
    be_to_n b == v x
) = ()

let encode_asn1_injective
  (x1: uint_32{0 < v x1})
  (x2: uint_32{0 < v x2})
:Lemma (
  encode_asn1_integer x1 == encode_asn1_integer x2
  ==>
  x1 == x2
)
= () // if (encode_asn1_integer x1 == encode_asn1_integer x2)

// let decode_asn1_integer
//   (bs: bytes{4 <= Seq.length bs /\ Seq.length bs <= 5})
// : option (x: uint_32{ 0 <= v x /\ v x < 4294967296 })
// = match Seq.length bs,
//         bs.[0],
//         bs.[0] `U8.div` 0x80uy,
//         bs.[1] `U8.div` 0x80uy
//   with
//   | 5, 0x00uy, _     , 0x01uy -> Some (decode_int32le (Seq.slice bs 1 5))
//   | 4, _     , 0x00uy, _      -> Some (decode_int32le bs)
//   | (*reject negative int*) _ -> None

// let filter_asn1_integer_weak
//   (bs: bytes{Seq.length bs == 4})
// : GTot bool
// = (v bs.[0]) / 0x80 = 0

// let synth_asn1_integer
//   (bs: bytes{Seq.length bs == 4})
// : GTot (x: uint_32{0 <= v x /\ v x < 4294967296})
// = decode_int32le
// match Seq.length bs with
//   | 4 -> decode_int32le bs
//   | 5 -> decode_int32le (Seq.slice bs 1 5)

let filter_asn1_integer
  (bs: bytes{Seq.length bs == 4 \/ Seq.length bs == 5})
: GTot bool
= Seq.length bs = 4 && (v bs.[0]) / 0x80 = 0 ||
  Seq.length bs = 5 && (v bs.[1]) / 0x80 = 1 && bs.[0] = 0x00uy

let c = normalize_term (n_to_le 4 100)

let asn1_int_bytes = bs: bytes{
  Seq.length bs == 4 /\ Seq.length bs == 5 /\
 ((v bs.[0]) >= 128 == 0 ==> Seq.length bs == 4 \/
  (v bs.[1]) >= 128 == 1 /\ bs.[0] == 0x00uy ==> Seq.length bs == 5)
}

let synth_asn1_integer
  (bs: asn1_int_bytes)
: GTot (x: uint_32{0 <= v x /\ v x < 4294967296})
= match Seq.length bs with
  | 4 -> decode_int32le bs
  | 5 -> decode_int32le (Seq.slice bs 1 5)

let synth_asn1_integer_injective ()
: Lemma (synth_injective synth_asn1_integer)
= synth_injective_intro' synth_asn1_integer (fun (x x': asn1_int_bytes) ->
  match Seq.length x with
  | 4 -> decode_int32le_injective x x'
  | 5 -> assert (x.[0] == x'.[0]);
         decode_int32le_injective (Seq.slice x 1 5) (Seq.slice x' 1 5)
)

open LowParse.Spec.SeqBytes

// let parse_asn1_integer (len: nat{len == 4 \/ len == 5})
// = parse_seq_flbytes len
//   `parse_filter`
//   filter_asn1_integer
//   `parse_synth`
//   synth_asn1_integer

// #push-options "--query_stats --z3rlimit 64 --max_fuel 64 --max_ifuel 64"

let encode_asn1_integer
  (x: uint_32{ 0 <= v x /\ v x < 4294967296 } )
: Tot asn1_int_bytes
= let v  = v x in
  let bs = n_to_le 4 v in
  if (v bs.[0]) / 0x80 = 0 then
  ( assert (bs.[0] == 0x00uy ==> Seq.length bs == 4)
   ; bs )
  else (* add a leading byte 0x00uy *)
  ( 0x00uy `Seq.cons` bs )

let decode_asn1_integer
  (bs: bytes{4 <= Seq.length bs /\ Seq.length bs <= 5})
: option (x: uint_32{ 0 <= v x /\ v x < 4294967296 })
= match Seq.length bs,
        bs.[0],
        (v bs.[0]) / 0x80,
        (v bs.[1]) / 0x80
  with
  | 5, 0x00uy, _   , 0x01 -> Some (decode_int32le (Seq.slice bs 1 5))
  | 4, _     , 0x00, _    -> Some (decode_int32le bs)
  | (*reject neg int*) _  -> None

#push-options "--query_stats --z3rlimit 64"
let decode_asn1_integer_correct ()
: Lemma (
  forall (x: uint_32{ 0 <= v x /\ v x < 4294967296 } ).
  let bs = encode_asn1_integer x in
  let x' = decode_asn1_integer bs in
  Some?.v x' == x
)
= ()
(*)
#push-options "--query_stats"
let decode_asn1_integer_injective
  (bs1: bytes{4 <= Seq.length bs1 /\ Seq.length bs1 <= 5})
  (bs2: bytes{4 <= Seq.length bs2 /\ Seq.length bs2 <= 5})
: Lemma (
  decode_asn1_integer bs1 == decode_asn1_integer bs2 /\
  Some? (decode_asn1_integer bs1)
  ==>
  Seq.length bs1 == Seq.length bs2)
= () if decode_asn1_integer bs1 = decode_asn1_integer bs2 &&
     Some? (decode_asn1_integer bs1) then
  ( if (Seq.length bs1) )

(*)
if (decode_asn1_integer bs1) = (decode_asn1_integer bs2) then
  (  )

#push-options "--query_stats --z3rlimit 64"
// let bi (): Lemma// (decode_asn1_integer (encode_asn1_integer 1ul) = Some 1ul) = ()
// ( (decode_asn1_integer (encode_asn1_integer 0ul)) == Some 0ul )
// = let b = encode_asn1_integer 0ul in
// reveal_le_to_n (encode_asn1_integer 0ul)

// assert (Seq.length (encode_asn1_integer 0ul) == 4)

(*)
let decode_asn1_integer_injective
  (bs1: bytes{4 <= Seq.length bs /\ Seq.length bs <= 5})
