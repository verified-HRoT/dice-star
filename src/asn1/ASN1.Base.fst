module ASN1.Base
module Bytes = LowParse.Bytes
module HI = Lib.IntTypes

let (.[]) = FStar.Seq.index

type asn1_type: Type =
| BOOLEAN
// | INTEGER
| NULL
| OCTET_STRING
// | BIT_STRING
// | OID
// | SEQUENCE

// let asn1_primitive_type = a: asn1_type{a <> SEQUENCE}

let the_asn1_type (a: asn1_type)
: Tot Type0
= (a': asn1_type{a == a'})

let datatype_of_asn1_type (a: asn1_type): Type
= match a with
  | BOOLEAN -> bool
  // | INTEGER -> HI.pub_uint32
  | NULL -> unit
  | OCTET_STRING -> Bytes.bytes

let asn1_length_t = n: nat{0 <= n /\ n <= 4294967295}
let asn1_length_min: n: asn1_length_t {forall (n':asn1_length_t). n <= n'} = 0
let asn1_length_max: n: asn1_length_t {forall (n':asn1_length_t). n >= n'} = 4294967295
let asn1_length_inbound (x: nat) (min max: asn1_length_t): bool
= min <= x && x <= max

let min_of_asn1_type
  (a: asn1_type)
: asn1_length_t
= match a with
  | BOOLEAN   -> 1
  | NULL -> 0
  | OCTET_STRING -> asn1_length_min

let max_of_asn1_type
  (a: asn1_type)
: asn1_length_t
= match a with
  | BOOLEAN   -> 1
  | NULL -> 0
  | OCTET_STRING -> asn1_length_max

let bound_of_asn1_type
  (a: asn1_type)
: (asn1_length_t * asn1_length_t)
= (min_of_asn1_type a, max_of_asn1_type a)

type asn1_value: Type =
| BOOLEAN_VALUE: b: bool -> asn1_value
| NULL_VALUE: n:unit -> asn1_value
| OCTET_STRING_VALUE: s: Bytes.bytes{true == asn1_length_inbound (Seq.length s) (min_of_asn1_type OCTET_STRING) (max_of_asn1_type OCTET_STRING)} -> asn1_value

// let asn1_proper_TL
//   (a: asn1_type)
//   (l: asn1_length_t)
// : Type0
// = let min, max = asn1_proper_length_of_tag a in
//   asn1_length_inbound l min max == true

// let asn1_TL = (a: asn1_type & l: asn1_length_t {asn1_proper_TL a l})
