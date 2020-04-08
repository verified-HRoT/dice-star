module ASN1.Low.TLV.Specialized

open ASN1.Base

open ASN1.Spec.Tag
open ASN1.Spec.Length
open ASN1.Spec.BOOLEAN
open ASN1.Spec.NULL
open ASN1.Spec.OCTET_STRING
open ASN1.Spec.SEQUENCE
open ASN1.Spec.TLV.Specialized

open LowParse.Low.Base
open LowParse.Low.Combinators

open ASN1.Low.Base
open ASN1.Low.Tag
open ASN1.Low.Length
open ASN1.Low.BOOLEAN
open ASN1.Low.NULL
open ASN1.Low.OCTET_STRING
open ASN1.Low.SEQUENCE

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module MB = LowStar.Monotonic.Buffer
module B = LowStar.Buffer
module Cast = FStar.Int.Cast

open FStar.Integers

/// TODO: Move to spec
let asn1_length_inbound_of_primitive_value
  (#_a: asn1_primitive_type)
  (value: datatype_of_asn1_type _a)
: GTot (b: bool { b == asn1_length_inbound_of_type _a (length_of_asn1_primitive_value value) })
= let min, max = asn1_length_bound_of_type _a in
  let length = length_of_asn1_primitive_value value in
  asn1_length_inbound length min max

let asn1_length_inbound_of_primitive_TLV
  (#_a: asn1_primitive_type)
  (value: datatype_of_asn1_type _a)
: GTot (b: bool)
= let min, max = asn1_length_bound_of_type _a in
  let length = length_of_asn1_primitive_TLV value in
  asn1_length_inbound length asn1_length_min asn1_length_max

/// Interface
///
let serialize32_asn1_TLV_backwards_of_type
  (_a: asn1_primitive_type)
: serializer32_backwards (serialize_asn1_TLV_of_type _a)
= match _a with
  | BOOLEAN      -> serialize32_asn1_boolean_TLV_backwards ()
  | NULL         -> serialize32_asn1_null_TLV_backwards ()
  | OCTET_STRING -> serialize32_asn1_octet_string_TLV_backwards ()

/// Example
///

/// Extension definition
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

/// Extension value parser
///
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

/// Extension value serializer
///
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


/// Extension TLV parser/serializer
///
let parse_inner_sequence
= parse_asn1_sequence_TLV serialize_inner_value

let parse_inner_sequence_unfold
= parse_asn1_sequence_TLV_unfold serialize_inner_value

let serialize_inner_sequence
: serializer parse_inner_sequence
= serialize_asn1_sequence_TLV serialize_inner_value

let serialize_inner_sequence_unfold
= serialize_asn1_sequence_TLV_unfold serialize_inner_value

/// Len computing functions for this extension
///
#push-options "--query_stats --z3rlimit 4"

let length_of_inner_t_value
  (x: inner_t)
: GTot (nat)
= Seq.length (serialize serialize_inner_value x)

let len_of_inner_t_unbounded
  (x: inner_t)
: Tot (len: option (asn1_int32_of_type SEQUENCE) {
  Some? len ==>
    v (Some?.v len) == Seq.length (serialize serialize_inner_value x)
})
= (* Prf*) serialize_inner_value_unfold x;
  let len_n1 = len_of_asn1_primitive_TLV_unbounded x.n1 in
  let len_s1 = len_of_asn1_primitive_TLV_unbounded x.s1 in
(* retuen *) len_n1 `safe_add` len_s1

let len_of_inner_t_inbound
  (x: inner_t { asn1_length_inbound_of_type SEQUENCE (Seq.length (serialize serialize_inner_value x)) } )
: Tot (len: asn1_int32_of_type SEQUENCE {
  v len == Seq.length (serialize serialize_inner_value x)
})
= (* Prf *) serialize_inner_value_unfold x;
  let len_n1 = len_of_asn1_primitive_TLV_inbound x.n1 in
  let len_s1 = len_of_asn1_primitive_TLV_inbound x.s1 in
(* return *) len_n1 + len_s1
#pop-options

let synth_inner_t_inverse_impl
  (x: inner_t)
: Tot (x': inner_t'{x' == synth_inner_t_inverse x})
= (x.n1, x.s1)

let serialize32_inner_value_backwards ()
: Tot (serializer32_backwards serialize_inner_value)
= serialize32_synth_backwards
  (* s32*) (serialize32_asn1_TLV_backwards_of_type NULL
            `serialize32_nondep_then_backwards`
            serialize32_asn1_TLV_backwards_of_type OCTET_STRING)
  (* f1 *) (synth_inner_t)
  (* g1 *) (synth_inner_t_inverse)
  (* g1'*) (synth_inner_t_inverse_impl)
  (* prf*) ()

let serialize32_inner_sequence_backwards
= serialize32_asn1_sequence_TLV_backwards
  (* s32*) (serialize32_inner_value_backwards ())
  (* len*) (len_of_inner_t_inbound)

/// TEST
///
open FStar.Tactics

#restart-solver
#push-options "--query_stats --z3rlimit 64"
let inner_t_serialization_test
  ()
: HST.Stack unit
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)
= HST.push_frame ();

  (* NOTE: Allocate a destination buffer. *)
  let dst_len = 50ul in
  let dst = B.alloca 0uy dst_len in
  let pos = dst_len in

  (* NOTE: Prove writability for buffer with trivial preorder. *)
  (* Prf *) let h0 = HST.get () in
  (* Prf *) writable_intro
            (* buf *) dst
            (*range*) 0 (B.length dst)
            (* mem *) h0
            (* prf *) () (fun s1 s2 -> ());

  (* NOTE: Define an extension instance `x`. *)
  let n: datatype_of_asn1_type NULL = () in
  let s: datatype_of_asn1_type OCTET_STRING = (|5ul, Seq.create 5 1uy|) in
  let x: inner_t = {n1 = n; s1 = s} in

  (* NOTE: Reason about the size of these extension instance `x`. *)
  (* TODO: We definitely should simplify these spec lemmas. *)
  (* Prf *) serialize_inner_value_unfold x;

  (* Prf *) serialize_asn1_null_TLV_unfold n;
  (* Prf *) parser_kind_prop_equiv parse_asn1_null_TLV_kind parse_asn1_null_TLV;
  (* Prf *) assert (length_of_asn1_primitive_TLV n == 2);

  (* Prf *) serialize_asn1_octet_string_TLV_unfold s;
  (* Prf *) serialize_the_asn1_tag_unfold OCTET_STRING OCTET_STRING;
  (* Prf *) serialize_asn1_length_unfold 5ul;
  (* Prf *) serialize_asn1_octet_string_V_unfold (parser_tag_of_octet_string s) s;
  (* Prf *) serialize_asn1_octet_string_unfold (v (dfst s)) s;
  (* Prf *) assert (length_of_asn1_primitive_TLV s == 1 + v (len_of_asn1_length 5ul) + 5);

  (* Prf *) serialize_inner_sequence_unfold x;
  (* Prf *) serialize_asn1_sequence_TL_unfold (parser_tag_of_asn1_sequence serialize_inner_value x);
  (* Prf *) serialize_the_asn1_tag_unfold SEQUENCE SEQUENCE;
  (* Prf *) serialize_asn1_length_unfold (len_of_asn1_primitive_TLV_inbound n + len_of_asn1_primitive_TLV_inbound s);
  (* Prf *) assert (asn1_length_inbound_of_type SEQUENCE (Seq.length (serialize serialize_inner_value x)));
  (* Prf *) assert (length_of_asn1_primitive_TLV n + length_of_asn1_primitive_TLV s == length_of_inner_t_value x);

  (* Prf *) serialize_asn1_sequence_value_unfold
              serialize_inner_value
              (parser_tag_of_asn1_sequence serialize_inner_value x)
              x;

  (* Prf *) assert ((serialize serialize_inner_sequence x) `Seq.equal`
                    ( (serialize (serialize_the_asn1_tag SEQUENCE) SEQUENCE)
                    `Seq.append` (serialize (serialize_asn1_length_of_type SEQUENCE) (len_of_inner_t_inbound x))
                    `Seq.append` (serialize (serialize_inner_value) x) ));

  (* Prf *) assert (Seq.length (serialize serialize_inner_sequence x) ==
                    ( Seq.length (serialize (serialize_the_asn1_tag SEQUENCE) SEQUENCE)
                    + Seq.length (serialize (serialize_asn1_length_of_type SEQUENCE) (len_of_inner_t_inbound x))
                    + Seq.length (serialize (serialize_inner_value) x) ));
  (* Prf *) assert (Seq.length (serialize serialize_inner_sequence x) ==
                    ( 1
                    + v (len_of_asn1_length (len_of_inner_t_inbound x))
                    + length_of_inner_t_value x ));

  (* Finally... *)
  (* Prf *) assert (Seq.length (serialize serialize_inner_sequence x) <= v pos /\ v pos <= B.length dst);

  (* NOTE: Serialization. *)
  (* Prf *) writable_weaken
            (* buf *) dst
            (*range*) 0 (B.length dst)
            (* mem *) h0
            (* from*) (v pos - length_of_inner_t_value x)
            (* to  *) (v pos);

  let offset = serialize32_inner_sequence_backwards
               (*val*) x
               (*dst*) dst
               (*pos*) pos in

  (* NOTE: Reason about the content of serialization. *)
  (* Prf *) let h1 = HST.get () in
  (* Prf *) assert (B.modifies (B.loc_buffer_from_to dst (pos - offset) pos) h0 h1);
  (* Prf *) assert (serialize serialize_inner_sequence x
                    `Seq.equal`
                    Seq.slice (B.as_seq h1 dst) (v (pos - offset)) (v pos));

  HST.pop_frame ()
#pop-options



open FStar.Tactics

#push-options "--query_stats --z3rlimit 32"

let rec gen_asn1_primitive_TLV_parser_kind
  (l: list asn1_primitive_type)
: parser_kind
= match l with
  | a1 :: l' -> (parse_asn1_TLV_kind_of_type a1
                `and_then_kind`
                gen_asn1_primitive_TLV_parser_kind l')
  | []      -> (parse_ret_kind)

let rec gen_asn1_primitive_TLV_parser_type
  (l: list asn1_primitive_type)
: Type0
= match l with
  | a1 :: l' -> (datatype_of_asn1_type a1 & gen_asn1_primitive_TLV_parser_type l')
  | []      -> unit

let rec gen_asn1_primitive_TLV_parser
  (l: list asn1_primitive_type)
: parser (gen_asn1_primitive_TLV_parser_kind l) (gen_asn1_primitive_TLV_parser_type l)
= match l with
  | a1 :: l' -> (parse_asn1_TLV_of_type a1
                `nondep_then`
                gen_asn1_primitive_TLV_parser l')
  | []      -> (parse_ret ())

let c = gen_asn1_primitive_TLV_parser [NULL; NULL; NULL; BOOLEAN]

type test_t =
| Test_t: (a: datatype_of_asn1_type NULL) -> (b: datatype_of_asn1_type OCTET_STRING) -> test_t

let inspect_test
  (se: sigelt)
: Tac unit
= let (.[]) = List.Tot.index in
  let r = lookup_typ (top_env ()) ["test_t"] in
    guard (Some? r);
  let Some se = r in
  let sv = inspect_sigelt se in
    guard (Sg_Inductive? sv);
  let Sg_Inductive name us params ty constructors = sv in
    guard (List.length constructors = 1);

  let constructor_r = lookup_typ (top_env ()) constructors.[0] in
    guard (Some? constructor_r);
  let constructor_sv = inspect_sigelt (Some?.v constructor_r) in
    guard (Sg_Constructor? constructor_sv);
  let Sg_Constructor name typ = constructor_sv in
  let indices = inspect_ln typ in
  _ by (dump "inspect"; exact (`()))
