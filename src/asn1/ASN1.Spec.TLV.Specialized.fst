module ASN1.Spec.TLV.Specialized

open ASN1.Base
open ASN1.Spec.Tag
open ASN1.Spec.Length
open ASN1.Spec.BOOLEAN
open ASN1.Spec.NULL
open ASN1.Spec.OCTET_STRING
open LowParse.Bytes

module I = FStar.Integers

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

/// Ad-hoc sequence parser/serializer
///

let parse_asn1_sequence_TL_kind
: parser_kind
= parse_asn1_tag_kind
  `and_then_kind`
  parse_asn1_length_kind_of_type SEQUENCE

let parse_asn1_sequence_TL
: parser parse_asn1_sequence_TL_kind (the_asn1_type SEQUENCE & asn1_int32_of_type SEQUENCE)
= parse_the_asn1_tag SEQUENCE
  `nondep_then`
  parse_asn1_length_of_type SEQUENCE

let serialize_asn1_sequence_TL
: serializer parse_asn1_sequence_TL
= serialize_the_asn1_tag SEQUENCE
  `serialize_nondep_then`
  serialize_asn1_length

#push-options "--query_stats --z3rlimit 32"
let safe_add
  (a b: option asn1_int32)
: Tot (option asn1_int32)
= let open FStar.Integers in
  if (Some?a && Some? b && (Some?.v a) <= asn1_int32_max - (Some?.v b)) then
  ( Some (Some?.v a + Some?.v b) )
  else
  ( None )

let len_of_asn1_primitive_TLV
  (#_a: asn1_primitive_type)
  (data: datatype_of_asn1_type _a)
: Tot (x: option asn1_int32{Some? x ==> (I.v (Some?.v x) == Seq.length (serialize (serialize_asn1_TLV_of_type _a) data))})
= let data_len = len_of_asn1_data _a data in
  let len_len = len_of_asn1_length data_len in
  let res = 1ul in
  Some 1ul `safe_add` Some len_len `safe_add` Some data_len

let parse_exact_bare
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (l: nat)
: Tot (bare_parser t)
= fun (input: bytes) ->
  if (Seq.length input < l) then
  ( None )
  else
  ( match parse p (Seq.slice input 0 l) with
    | Some (v, n) -> if n = l then
                     ( Some (v, (l <: consumed_length input)) )
                     else
                     ( None )
    | None        -> None )

let parse_exact_bare_injective_prf
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (l: nat)
  (input1: bytes)
  (input2: bytes)
: Lemma
  (requires (injective_precond (parse_exact_bare p l) input1 input2))
  (ensures (injective_postcond (parse_exact_bare p l) input1 input2))
= if (Seq.length input1 < l) then
  ( () )
  else
  ( match parse p (Seq.slice input1 0 l), parse p (Seq.slice input2 0 l) with
    | Some (v1, n1), Some (v2, n2) -> if n1 = l && n2 = l then
                                      ( parser_kind_prop_equiv k p;
                                        assert (injective_postcond p (Seq.slice input1 0 l) (Seq.slice input2 0 l)) )
                                      else
                                      ( () )
    | _        -> () )

let parse_exact_bare_injective
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (l: nat)
: Lemma (
  injective (parse_exact_bare p l)
)
= Classical.forall_intro_2 (
    fun (s1 s2: bytes) ->
      Classical.move_requires_2 (parse_exact_bare_injective_prf p l) s1 s2
  )

let parse_exact_kind
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (l: nat)
: parser_kind = {
  parser_kind_low = l;
  parser_kind_high = Some l;
  parser_kind_subkind = None;
  parser_kind_metadata = None
}

let parse_exact_correct
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (l: nat)
: Lemma (
  parser_kind_prop (parse_exact_kind p l) (parse_exact_bare p l)
)
= parser_kind_prop_equiv (parse_exact_kind p l) (parse_exact_bare p l);
  parse_exact_bare_injective p l

let parse_exact
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (l: nat)
: parser (parse_exact_kind p l) t
= parse_exact_correct p l;
  parse_exact_bare p l


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

let len_of_inner_t
  (x: inner_t)
: Tot (option (asn1_int32_of_type SEQUENCE))
= let len_n1 = len_of_asn1_primitive_TLV x.n1 in
  let len_s1 = len_of_asn1_primitive_TLV x.s1 in
  len_n1 `safe_add` len_s1

let parse_inner
: parser _ inner_t
= parse_asn1_TLV_of_type NULL
  `nondep_then`
  parse_asn1_TLV_of_type OCTET_STRING
  `parse_synth`
  synth_inner_t

let serialize_inner
: serializer parse_inner
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

let parse_exact_kind_weak = {
  parser_kind_low = asn1_length_min;
  parser_kind_high = Some asn1_length_max;
  parser_kind_subkind = None;
  parser_kind_metadata = None
}

let lmm (b: bytes): Lemma
  (requires (Some? (parse parse_inner b)))
  (ensures (let Some (v, l) = parse parse_inner b in
            Some? (len_of_inner_t v)))
= ()

#push-options "--query_stats --z3rlimit 64"
let lm (): Lemma (
  let s = Seq.create 5 1uy in
  let i = {n1 = (); s1 = (|5ul, s|)} in
  let pe = parse_exact parse_inner (I.v (Some?.v (len_of_inner_t i))) in
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
            parse_exact parse_inner (I.v (snd x))) in
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
