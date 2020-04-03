module ASN1.Spec.INTEGER

open LowParse.Spec.Base
open LowParse.Spec.Combinators
open LowParse.Spec.Int

open ASN1.Base

(* INTEGER *)
(* 1) Positive: (Leading 0x00uy ++) content
   2) Negative: b[0] & 0x80uy != 0 *)
open LowParse.Spec.Int32le
open FStar.Endianness
open FStar.Integers

(* NOTE: Big Endian *)
(* FIXME: Excluded 0 for now, Mbed TLS's parser said that
          it should be represented as 020100 for INTEGER
          or 0A0100 for ENUMERATED *)
#push-options "--query_stats --z3rlimit 64"
// let remove_leading_zeros'
//   (bs: bytes)
// : (bs': bytes{Seq.length bs' > 0 ==> bs'.[0] =!= 0x00uy})

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
    ( false_elim () ) in
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
