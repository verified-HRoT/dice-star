module ASN1.Spec.TLV.Specialized

open LowParse.Spec.Base
open LowParse.Spec.Combinators

open ASN1.Base
open ASN1.Spec.Tag
open ASN1.Spec.Length
open ASN1.Spec.BOOLEAN
open ASN1.Spec.NULL
open ASN1.Spec.OCTET_STRING
open ASN1.Spec.SEQUENCE
open LowParse.Bytes

open FStar.Integers

/// Interface
let parse_asn1_TLV_kind_of_type
  (_a: asn1_primitive_type)
: parser_kind
= match _a with
  | BOOLEAN      -> parse_asn1_boolean_TLV_kind
  | NULL         -> parse_asn1_null_TLV_kind
  | OCTET_STRING -> parse_asn1_octet_string_TLV_kind

let parse_asn1_TLV_of_type
  (_a: asn1_primitive_type)
: parser (parse_asn1_TLV_kind_of_type _a) (datatype_of_asn1_type _a)
= match _a with
  | BOOLEAN      -> parse_asn1_boolean_TLV
  | NULL         -> parse_asn1_null_TLV
  | OCTET_STRING -> parse_asn1_octet_string_TLV

let serialize_asn1_TLV_of_type
  (_a: asn1_primitive_type)
: serializer (parse_asn1_TLV_of_type _a)
= match _a with
  | BOOLEAN      -> serialize_asn1_boolean_TLV
  | NULL         -> serialize_asn1_null_TLV
  | OCTET_STRING -> serialize_asn1_octet_string_TLV

// let parse_asn1_TLV_of_type_unfold
//   (_a: asn1_primitive_type)
// : GTot (bytes -> _)
// = match _a with
//   | BOOLEAN      -> (parse_asn1_boolean_TLV_unfold)
//   | NULL         -> (parse_asn1_null_TLV_unfold)
//   | OCTET_STRING -> (parse_asn1_octet_string_TLV_unfold)

// let serialize_asn1_TLV_of_type_unfold
//   (_a: asn1_primitive_type)
// : GTot (datatype_of_asn1_type _a -> _)
// = match _a with
//   | BOOLEAN      -> (serialize_asn1_boolean_TLV_unfold)
//   | NULL         -> (serialize_asn1_null_TLV_unfold)
//   | OCTET_STRING -> (serialize_asn1_octet_string_TLV_unfold)


#push-options "--query_stats --z3rlimit 32"
let safe_add
  (a b: option asn1_int32)
: Tot (c: option asn1_int32 {
          Some?a /\ Some?b /\ Some? c ==>
            v (Some?.v c) == v (Some?.v a) + v (Some?.v b)
  })
= let open FStar.Integers in
  if (Some?a && Some? b && (Some?.v a) <= asn1_int32_max - (Some?.v b)) then
  ( Some (Some?.v a + Some?.v b) )
  else
  ( None )
#pop-options

// private
// let serialize_asn1_value_of_type
//   (#_a: asn1_primitive_type)
//   (value: datatype_of_asn1_type _a)
// : GTot (s: bytes)
// = match _a with
//   | BOOLEAN      -> serialize serialize_asn1_boolean value
//   | NULL         -> serialize serialize_asn1_null value
//   | OCTET_STRING -> let (|len, s|) = value <: datatype_of_asn1_type OCTET_STRING in
//                     let l = v len in
//                     serialize_asn1_octet_string_unfold l value;
//                     serialize (serialize_asn1_octet_string l) value

/// Length Spec of ASN.1 [VALUE] of primitive types
///
let length_of_asn1_primitive_value
  (#_a: asn1_primitive_type)
  (value: datatype_of_asn1_type _a)
: GTot (length: asn1_length_t)
= Seq.length (
    match _a with
    | BOOLEAN      -> serialize serialize_asn1_boolean value
    | NULL         -> serialize serialize_asn1_null value
    | OCTET_STRING -> serialize (serialize_asn1_octet_string (v (dfst (value <: datatype_of_asn1_type OCTET_STRING)))) value)

/// Length Spec of ASN.1 Primitive [TAG, LEN, VALUE] of primitive types
///
let length_of_asn1_primitive_TLV
  (#_a: asn1_primitive_type)
  (value: datatype_of_asn1_type _a)
: GTot (length: nat)
= Seq.length (serialize (serialize_asn1_TLV_of_type _a) value)

/// Len Impl of ASN.1 [VALUE] of primitive types
///
let len_of_asn1_primitive_value
  (#_a: asn1_primitive_type)
  (value: datatype_of_asn1_type _a)
: Tot (len: asn1_int32_of_type _a { v len == length_of_asn1_primitive_value value })
= match _a with
  | BOOLEAN      -> 1ul
  | NULL         -> 0ul
  | OCTET_STRING -> let (|len, s|) = value <: datatype_of_asn1_type OCTET_STRING in
                    let l = v len in
                    (* Prf *) serialize_asn1_octet_string_unfold l value;
                    dfst (value <: datatype_of_asn1_type OCTET_STRING)



#push-options "--query_stats --z3rlimit 32"

/// Length Spec of ASN.1 Primitive [TAG, LEN, VALUE] of primitive types
///
let len_of_asn1_primitive_TLV_unbounded
  (#_a: asn1_primitive_type)
  (value: datatype_of_asn1_type _a)
: Tot (len: option asn1_int32 {
         Some? len ==>
           (v (Some?.v len) == length_of_asn1_primitive_TLV value)
  })
= (* Prf *) (match _a with
             | BOOLEAN      -> (serialize_asn1_boolean_TLV_unfold      (value <: datatype_of_asn1_type BOOLEAN))
             | NULL         -> (serialize_asn1_null_TLV_unfold         (value <: datatype_of_asn1_type NULL))
             | OCTET_STRING -> (serialize_asn1_octet_string_TLV_unfold (value <: datatype_of_asn1_type OCTET_STRING)));

  let value_len = len_of_asn1_primitive_value value in
  (* Prf *) assert (v value_len == length_of_asn1_primitive_value value);

  let len_len = len_of_asn1_length value_len in

  let tag_len = 1ul in

  (* Prf *) assert (v tag_len + v len_len + v value_len == Seq.length (serialize (serialize_asn1_TLV_of_type _a) value));

(* return *) Some tag_len `safe_add` Some len_len `safe_add` Some value_len



let len_of_asn1_primitive_TLV_inbound
  (#_a: asn1_primitive_type)
  (value: datatype_of_asn1_type _a {
    asn1_length_inbound (length_of_asn1_primitive_TLV value) asn1_length_min asn1_length_max
  })
: Tot (len: asn1_int32 { v len == length_of_asn1_primitive_TLV value })
= (* Prf *) (match _a with
             | BOOLEAN      -> (serialize_asn1_boolean_TLV_unfold (value <: datatype_of_asn1_type BOOLEAN))
             | NULL         -> (serialize_asn1_null_TLV_unfold (value <: datatype_of_asn1_type NULL))
             | OCTET_STRING -> (serialize_asn1_octet_string_TLV_unfold (value <: datatype_of_asn1_type OCTET_STRING)));

  let value_len = len_of_asn1_primitive_value value in
  (* Prf *) assert (v value_len == length_of_asn1_primitive_value value);

  let len_len = len_of_asn1_length value_len in

  let tag_len = 1ul in

  (* Prf *) assert (v tag_len + v len_len + v value_len == Seq.length (serialize (serialize_asn1_TLV_of_type _a) value));

(* return *) tag_len + len_len + value_len
#pop-options
(*)
/// Example
///
type inner_t = {
  n1: datatype_of_asn1_type NULL;
  s1: datatype_of_asn1_type OCTET_STRING
}

let inner_t' = (
  datatype_of_asn1_type NULL &
  datatype_of_asn1_type OCTET_STRING
)

let synth_inner_t
  (x': inner_t')
: GTot (inner_t)
= let n1, s1 = x' in
  {n1 = n1; s1 = s1}

let synth_inner_t_inverse
  (x: inner_t)
: GTot (x': inner_t'{x == synth_inner_t x'})
= (x.n1, x.s1)

let parse_inner_value
: parser _ inner_t
= parse_asn1_TLV_of_type NULL
  `nondep_then`
  parse_asn1_TLV_of_type OCTET_STRING
  `parse_synth`
  synth_inner_t

let parse_inner_value_unfold
  (input: bytes)
: Lemma (
  parse parse_inner_value input ==
 (match parse (parse_asn1_TLV_of_type NULL) input with
  | None -> None
  | Some (v_null, consumed_null) ->
      (let input' = Seq.slice input consumed_null (Seq.length input) in
       match parse (parse_asn1_TLV_of_type OCTET_STRING) input' with
       | None -> None
       | Some (v_octet_string, consumed_octet_string) ->
           (Some ( synth_inner_t (v_null, v_octet_string)
                 , (consumed_null + consumed_octet_string <: consumed_length input))))))
= nondep_then_eq
  (* p1 *) (parse_asn1_TLV_of_type NULL)
  (* p2 *) (parse_asn1_TLV_of_type OCTET_STRING)
  (* in *) (input);
  parse_synth_eq
  (* p1 *) (parse_asn1_TLV_of_type NULL
            `nondep_then`
            parse_asn1_TLV_of_type OCTET_STRING)
  (* f2 *) (synth_inner_t)
  (* in *) (input)

let serialize_inner_value
: serializer parse_inner_value
= serialize_synth
  (* p1 *) (parse_asn1_TLV_of_type NULL
            `nondep_then`
            parse_asn1_TLV_of_type OCTET_STRING)
  (* f1 *) (synth_inner_t)
  (* s1 *) (serialize_asn1_TLV_of_type NULL
            `serialize_nondep_then`
            serialize_asn1_TLV_of_type OCTET_STRING)
  (* g1 *) (synth_inner_t_inverse)
  (* Prf*) ()

let serialize_inner_value_unfold
  (value: inner_t)
: Lemma (
  serialize serialize_inner_value value ==
  serialize (serialize_asn1_TLV_of_type NULL) value.n1
  `Seq.append`
  serialize (serialize_asn1_TLV_of_type OCTET_STRING) value.s1)
= serialize_nondep_then_eq
  (* s1 *) (serialize_asn1_TLV_of_type NULL)
  (* s2 *) (serialize_asn1_TLV_of_type OCTET_STRING)
  (* val*) (synth_inner_t_inverse value);
  serialize_synth_eq
  (* p1 *) (parse_asn1_TLV_of_type NULL
            `nondep_then`
            parse_asn1_TLV_of_type OCTET_STRING)
  (* f2 *) (synth_inner_t)
  (* s1 *) (serialize_asn1_TLV_of_type NULL
            `serialize_nondep_then`
            serialize_asn1_TLV_of_type OCTET_STRING)
  (* g1 *) (synth_inner_t_inverse)
  (* prf*) ()
  (* val*) (value)

let parse_inner_sequence
= parse_asn1_sequence_TLV serialize_inner_value

let parse_inner_sequence_unfold
= parse_asn1_sequence_TLV_unfold serialize_inner_value

let serialize_inner_sequence
: serializer parse_inner_sequence
= serialize_asn1_sequence_TLV serialize_inner_value

let serialze_inner_sequence_unfold
= serialize_asn1_sequence_TLV_unfold serialize_inner_value


#push-options "--query_stats --z3rlimit 4"
let len_of_inner_t
  (x: inner_t)
: Tot (len: option (asn1_int32_of_type SEQUENCE) {
  Some? len ==> v (Some?.v len) == Seq.length (serialize serialize_inner_value x)
})
= let len_n1 = len_of_asn1_primitive_TLV_unbounded x.n1 in
  let len_s1 = len_of_asn1_primitive_TLV_unbounded x.s1 in
  serialize_inner_value_unfold x;
  len_n1 `safe_add` len_s1
#pop-options
(*)
#restart-solver
#push-options "--query_stats --z3rlimit 16"
let parse_inner_sequence_test
  ()
=
  let x = {
    n1 = ();
    s1 = (|3ul, Seq.create 3 9uy|)
  } in
  assert (Some? (len_of_inner_t x));
  assert (asn1_length_inbound_of_type SEQUENCE (Seq.length (serialize serialize_inner_value x)));
  let raw_seq =
    (((serialize (serialize_the_asn1_tag SEQUENCE) SEQUENCE
    `Seq.append`
    serialize (serialize_asn1_length_of_type SEQUENCE) (Some?.v (len_of_inner_t x)))
    `Seq.append`
    serialize_asn1_null_TLV x.n1)
    `Seq.append`
    serialize_asn1_octet_string_TLV x.s1)
  in
  let px = parse parse_inner_sequence raw_seq in
  and_then_eq
()
  serialize_the_asn1_tag_unfold SEQUENCE SEQUENCE;
  serialize_u8_spec (synth_the_asn1_tag_inverse SEQUENCE SEQUENCE);
  serialize_u8_spec' (synth_the_asn1_tag_inverse SEQUENCE SEQUENCE);
  serialize_asn1_length_of_type_unfold SEQUENCE (Some?.v (len_of_inner_t x));
  serialize_asn1_null_TLV_unfold x.n1;
  serialize_asn1_octet_string_TLV_unfold x.s1;

  parse_inner_sequence_unfold raw_seq;
  assert (raw_seq.[0] == (serialize (serialize_the_asn1_tag SEQUENCE) SEQUENCE).[0]);
  parse_asn1_sequence_TL_unfold raw_seq;
  parse_the_asn1_tag_unfold SEQUENCE raw_seq;
  parse_u8_spec raw_seq;
  parse_u8_spec' raw_seq;
  assert (raw_seq.[0] == 0x30uy);
  let px_raw = parse (parse_u8) raw_seq in
  assert (Some? px_raw);
  parse_u8_spec' raw_seq;

  parse_asn1_sequence_TL_unfold raw_seq;
  serialize_asn1_sequence_TL_unfold (SEQUENCE, Some?.v (len_of_inner_t x));
  serialize_asn1_sequence_TLV_unfold serialize_inner_value x;
  parse_asn1_sequence_TLV_unfold serialize_inner_value raw_seq;
  let px_t  = parse (parse_the_asn1_tag SEQUENCE) raw_seq in
  assert (Some? px_t);

  parse_inner_value_unfold raw_seq;
  serialize_inner_value_unfold x;

  // let px_tl = parse parse_asn1_sequence_TL raw_seq in
  // // let pseq = parse (parse_inner_sequence) raw_seq in
  // assert (Some? px_tl);

()

let lmm (b: bytes): Lemma
  (requires (Some? (parse parse_inner b)))
  (ensures (let Some (v, l) = parse parse_inner b in
            Some? (len_of_inner_t v)))
= ()

#push-options "--query_stats --z3rlimit 64"
let lm (): Lemma (
  let s = Seq.create 5 1uy in
  let i = {n1 = (); s1 = (|5ul, s|)} in
  let pe = parse_exact parse_inner (v (Some?.v (len_of_inner_t i))) in
  let sx = serialize serialize_inner i in
  let px = parse pe sx in
  (Some? px) /\ (len_of_inner_t i) == Some 9ul
)
= ()


(*)
parse_asn1_tag_unfold sx;
  serialize_asn1_tag_unfold BOOLEAN

let parser_tag_of_sequence
  (x: inner_t{Some? (len_of_inner_t x)})
: GTot (the_asn1_type SEQUENCE * asn1_int32_of_type SEQUENCE)
= (SEQUENCE, (Some?.v (len_of_inner_t x)))

let g (t: nat * nat)
= let x, y = t in
  Seq.create x 1uy <: s:bytes{Seq.length s == x}

let parser_inner_trick
  (t: (the_asn1_type SEQUENCE * asn1_int32_of_type SEQUENCE))
= let SEQUENCE, len = t in

let parse_inner_TLV
= let p = (fun (x: (the_asn1_type SEQUENCE * asn1_int32_of_type SEQUENCE)) ->
            // parse_exact_kind_weak
            // `weaken`
            parse_exact parse_inner (v (snd x))) in
  // assume (and_then_cases_injective p);
  parse_tagged_union
  (* pt *) (parse_the_asn1_tag SEQUENCE
            `nondep_then`
            parse_asn1_length_of_type SEQUENCE)
  (* tg *) (parser_tag_of_sequence)
  (* p  *) (p)

let serialize_inner_TLV
= ()

type outer_t = {
  b: datatype_of_asn1_type BOOLEAN;
  inner: inner_t;
  s: datatype_of_asn1_type OCTET_STRING
}

(*)
let len_of_outter_t
  (x: outer_t)
: Tot (option (asn1_int32_of_type SEQUENCE))
= let len_b = len_of_asn1_primitive_TLV x.b in
  if (Some? len_b) then
  ( let len_inner =  )
