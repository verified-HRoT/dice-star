module ASN1.Test.Helpers

open LowParse.Spec.Base
open LowParse.Low.Base
open ASN1.Base
open ASN1.Spec
open ASN1.Low

open LowStar.Printf
open LowStar.Comment
open LowStar.Failure

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module MB = LowStar.Monotonic.Buffer
module B = LowStar.Buffer
module C = C

open FStar.Integers

val buffer_eq
  (l: uint_32)
  (b1: B.lbuffer uint_8 (v l))
  (b2: B.lbuffer uint_8 (v l))
: HST.Stack bool
  (requires fun h ->
    B.(live h b1 /\ live h b2 /\
       length b1 == length b2 /\ length b2 == v l))
  (ensures fun h0 r h1 ->
    B.(modifies loc_none h0 h1 /\
       r == (as_seq h0 b1 = as_seq h1 b1)) )

val mbedtls_parse_BOOLEAN
  (buf: B.buffer uint_8)
  (len: size_t)
  (pos: size_t)
: HST.Stack (unit)
  (requires fun h ->
    B.live h buf /\
    B.length buf == v len /\
    0ul <= pos /\ pos < len)
  (ensures fun h r h1 ->
    // let seq = Seq.slice (B.as_seq h buf) (v pos) (v len) in
    // let px = parse (parse_asn1_TLV_of_type BOOLEAN) seq in
    B.modifies B.loc_none h h1
    // (Some? px ==> (let (x, l) = Some?.v px in x == r /\ l == 3))
    )

val mbedtls_parse_INTEGER
  (buf: B.buffer uint_8)
  (len: size_t)
  (pos: size_t)
: HST.Stack (unit)
  (requires fun h ->
    B.live h buf /\
    B.length buf == v len /\
    0ul <= pos /\ pos < len)
  (ensures fun h r h1 ->
    // let seq = Seq.slice (B.as_seq h buf) (v pos) (v len) in
    // let px = parse (parse_asn1_TLV_of_type INTEGER) seq in
    B.modifies B.loc_none h h1
    // (Some? px ==> (let (x, l) = Some?.v px in x == r))
    )

val mbedtls_parse_ASN1_NULL
  (buf: B.buffer uint_8)
  (len: size_t)
  (pos: size_t)
: HST.Stack (unit)
  (requires fun h ->
    B.live h buf /\
    B.length buf == v len /\
    0ul <= pos /\ pos < len)
  (ensures fun h r h1 ->
    // let seq = Seq.slice (B.as_seq h buf) (v pos) (v len) in
    // let px = parse (parse_asn1_TLV_of_type ASN1_NULL) seq in
    B.modifies B.loc_none h h1
    // (Some? px ==> (let (x, l) = Some?.v px in x == r /\ l == 0))
    )

val mbedtls_parse_OCTET_STRING
  (buf: B.buffer uint_8)
  (len: size_t)
  (pos: size_t)
: HST.Stack (unit)
  (requires fun h ->
    B.live h buf /\
    B.length buf == v len /\
    0ul <= pos /\ pos < len)
  (ensures fun h r h1 ->
    // let seq = Seq.slice (B.as_seq h buf) (v pos) (v len) in
    // let px = parse (parse_asn1_TLV_of_type OCTET_STRING) seq in
    B.modifies B.loc_none h h1
    // (Some? px ==> (let (x, l) = Some?.v px in x == r))
    )

val mbedtls_parse_BIT_STRING
  (buf: B.buffer uint_8)
  (len: size_t)
  (pos: size_t)
: HST.Stack (unit)
  (requires fun h ->
    B.live h buf /\
    B.length buf == v len /\
    0ul <= pos /\ pos < len)
  (ensures fun h r h1 ->
    // let seq = Seq.slice (B.as_seq h buf) (v pos) (v len) in
    // let px = parse (parse_asn1_TLV_of_type BIT_STRING) seq in
    B.modifies B.loc_none h h1
    // (Some? px ==> (let (x, l) = Some?.v px in x == r))
    )

val mbedtls_parse_OID
  (buf: B.buffer uint_8)
  (len: size_t)
  (pos: size_t)
: HST.Stack (unit)
  (requires fun h ->
    B.live h buf /\
    B.length buf == v len /\
    0ul <= pos /\ pos < len)
  (ensures fun h r h1 ->
    // let seq = Seq.slice (B.as_seq h buf) (v pos) (v len) in
    // let px = parse (parse_asn1_TLV_of_type OCTET_STRING) seq in
    B.modifies B.loc_none h h1
    // (Some? px ==> (let (x, l) = Some?.v px in x == r))
    )

// let test_asn1_serializer
//   (a: asn1_primitive_type)
//   (dst_size: uint_32)
//   (dst: B.buffer uint_8 {B.length dst == v dst_size})
//   (question: datatype_of_asn1_type a {length_of_asn1_primitive_TLV question <= v dst_size})
//   (solution_len: asn1_TLV_int32_of_type a)
//   (solution: B.buffer uint_8 {B.length solution == v solution_len /\
//                               v solution_len == length_of_asn1_primitive_TLV question})
// : HST.Stack (bool)
//   (requires fun h ->
//     B.live h solution /\ B.live h dst /\ B.disjoint solution dst /\
//     length_of_asn1_primitive_TLV question <= v dst_size /\
//     B.length solution = length_of_asn1_primitive_TLV question)
//   (ensures fun h0 r h1 ->
//     B.modifies (B.loc_buffer dst) h0 h1)
//     // r == (B.as_seq h0 solution = serialize (serialize_asn1_TLV_of_type a) question))
// = HST.push_frame ();

//   comment "writing 'answer' into `dst`";
//   let answer_len = serialize32_asn1_TLV_backwards_of_type
//                    (* ASN1 Type *) a
//                    (* ASN1 Value*) question
//                    (*    dst    *) dst
//                    (*    pos    *) dst_size in
//   let asnwer = B.sub dst (dst_size - answer_len) answer_len in

//   let result = if (answer_len = solution_len) then
//                ( true )
//                // ( dummy_memcmp
//                //   (* b1 *) asnwer
//                //   (* b2 *) solution
//                //   (* l  *) answer_len )
//                else
//                ( false ) in

//   HST.pop_frame ();

// (* return *) result
