module ASN1.Base
open FStar.Integers

let (.[]) = FStar.Seq.index
let byte = uint_8
let bytes = Seq.seq byte
let lbytes = Seq.Properties.lseq byte

type asn1_type: Type =
| BOOLEAN
// | INTEGER
| NULL
| OCTET_STRING
// | BIT_STRING
// | OID
| SEQUENCE

let the_asn1_type (a: asn1_type)
: Tot Type
= (a': asn1_type{a == a'})

let asn1_primitive_type
= (a: asn1_type{a =!= SEQUENCE})

let asn1_length_t = n: nat{0 <= n /\ n <= 4294967295}
let asn1_length_min: n: asn1_length_t {forall (n':asn1_length_t). n <= n'} = 0
let asn1_length_max: n: asn1_length_t {forall (n':asn1_length_t). n >= n'} = 4294967295
let asn1_length_inbound (x: nat) (min max: asn1_length_t): bool
= min <= x && x <= max

let asn1_length_min_of_type
  (a: asn1_type)
: asn1_length_t
= match a with
  | BOOLEAN   -> 1
  | NULL -> 0
  | OCTET_STRING -> asn1_length_min
  | SEQUENCE -> asn1_length_min

let asn1_length_max_of_type
  (a: asn1_type)
: asn1_length_t
= match a with
  | BOOLEAN   -> 1
  | NULL -> 0
  | OCTET_STRING -> asn1_length_max
  | SEQUENCE -> asn1_length_max

let asn1_length_bound_of_type
  (a: asn1_type)
: (asn1_length_t & asn1_length_t)
= (asn1_length_min_of_type a, asn1_length_max_of_type a)

let asn1_length_inbound_of_type
  (a: asn1_type) (x: nat)
: bool
= let min, max = asn1_length_bound_of_type a in
  asn1_length_inbound x min max

let asn1_int32 = LowParse.Spec.BoundedInt.bounded_int32 asn1_length_min asn1_length_max
let asn1_int32_min: i: asn1_int32 {forall (i': asn1_int32). i <= i'} = 0ul
let asn1_int32_max: i: asn1_int32 {forall (i': asn1_int32). i >= i'} = 4294967295ul

let asn1_int32_of_type
  (_a: asn1_type)
= let min, max = asn1_length_min_of_type _a, asn1_length_max_of_type _a in
  LowParse.Spec.BoundedInt.bounded_int32 min max

let asn1_int32_min_of_type
  (a: asn1_type)
: asn1_int32
= match a with
  | BOOLEAN   -> 1ul
  | NULL -> 0ul
  | OCTET_STRING -> asn1_int32_min
  | SEQUENCE -> asn1_int32_min

let asn1_int32_max_of_type
  (a: asn1_type)
: asn1_int32
= match a with
  | BOOLEAN   -> 1ul
  | NULL -> 0ul
  | OCTET_STRING -> asn1_int32_max
  | SEQUENCE -> asn1_int32_max

let asn1_int32_bound_of_type
  (a: asn1_type)
: (asn1_int32 & asn1_int32)
= (asn1_int32_min_of_type a, asn1_int32_max_of_type a)

///
let weak_kind_of_type
  (a: asn1_type)
: LowParse.Spec.Base.parser_kind
= let min, max = asn1_length_bound_of_type a in
  LowParse.Spec.Base.strong_parser_kind min max None

///
unfold
let datatype_of_asn1_type (a: asn1_primitive_type): Type
= match a with
  | BOOLEAN -> bool
  | NULL -> unit
  | OCTET_STRING -> (len: asn1_int32_of_type OCTET_STRING & s: bytes {Seq.length s == v len})

type asn1_value: Type =
| BOOLEAN_VALUE: b: bool -> asn1_value
| NULL_VALUE: n: unit -> asn1_value
| OCTET_STRING_VALUE: len: asn1_int32_of_type OCTET_STRING (* NOTE: Carrying length here for low-level operations. *)
                   -> s: bytes{v len == Seq.length s}
                   -> asn1_value

unfold
let asn1_value_of_type (a: asn1_primitive_type): Type
= match a with
  | BOOLEAN      -> value: asn1_value{BOOLEAN_VALUE? value}
  | NULL         -> value: asn1_value{NULL_VALUE? value}
  | OCTET_STRING -> value: asn1_value{OCTET_STRING_VALUE? value}

let asn1_boolean = value: asn1_value{BOOLEAN_VALUE? value}
let asn1_null = value: asn1_value{NULL_VALUE? value}
let asn1_octet_string = value: asn1_value{OCTET_STRING_VALUE? value}

let len_of_asn1_data
  (_a: asn1_primitive_type)
  (x: datatype_of_asn1_type _a)
: Tot (asn1_int32_of_type _a)
= match _a with
  | BOOLEAN      -> 1ul
  | NULL         -> 0ul
  | OCTET_STRING -> dfst (x <: datatype_of_asn1_type OCTET_STRING)

let len_of_asn1_value
  (value: asn1_value)
: asn1_int32
= match value with
  | BOOLEAN_VALUE          b -> 1ul
  | NULL_VALUE             n -> 0ul
  | OCTET_STRING_VALUE len s -> len
