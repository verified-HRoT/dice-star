module ASN1.Spec.Value.BigInteger

open ASN1.Spec.Base

open ASN1.Base
open ASN1.Spec.Tag
open ASN1.Spec.Length
open ASN1.Spec.Bytes32
open LowParse.Spec.DER

open FStar.Integers

module U32 = FStar.UInt32
module B32 = FStar.Bytes

(*

  encoded -----parse------>  decoded
   bytes  <---serialize--- octet string
*)

unfold
let big_integer_as_octet_string_t
= x: datatype_of_asn1_type OCTET_STRING
  { let (.[]) = B32.get in
      v (dfst x) > 0 /\                    // no nil
    ( if (v (dfst x) > 1) then
      ( (dsnd x).[0ul] =!= 0x00uy )        // no leading zero byte if length > 1
      else ( True ) ) /\
    ( if ((dsnd x).[0ul] >= 0x80uy) then   // leave one space for leading zero byte
      ( v (dfst x) <= asn1_length_max - 7 )
      else ( True ) ) }

unfold
[@@ "opaque_to_smt"]
let asn1_value_length_of_big_integer
= l: asn1_length_t { 1 <= l /\ l <= asn1_length_max - 6}

unfold
[@@ "opaque_to_smt"]
let asn1_value_int32_of_big_integer
= n: U32.t {asn1_int32_inbounds 1 (asn1_length_max - 6) n}

unfold
[@@ "opaque_to_smt"]
let asn1_TLV_length_of_big_integer
= l: asn1_length_t { 3 <= l /\ l <= asn1_length_max }

unfold
[@@ "opaque_to_smt"]
let asn1_TLV_int32_of_big_integer
= n: U32.t {asn1_int32_inbounds 3 asn1_length_max n}

unfold
let valid_big_integer_as_octet_string_prop
  (len: asn1_value_int32_of_big_integer)
  (x: big_integer_as_octet_string_t)
: Type0
= let (.[]) = B32.get in
  v (dfst x) > 0 /\
  ( if v len = 1 then
    ( v (dfst x) == v len /\ (dsnd x).[0ul] < 0x80uy )
    else if ((dsnd x).[0ul] >= 0x80uy) then
    ( v (dfst x) == v len - 1 )
    else
    ( v (dfst x) == v len /\ (dsnd x).[0ul] > 0x00uy ) )

(* ZT: Exposing them because one lemma needs `synth_..._inverse`. *)
let filter_big_integer_as_octet_string
  (len: asn1_value_int32_of_big_integer)
  (s32: B32.lbytes32 len)
: GTot bool
= let (.[]) = B32.get in
  v len > 0 &&
  ( if (v len = 1) then
    ( s32.[0ul] < 0x80uy )
    else if (s32.[0ul] = 0x00uy) then
    ( s32.[1ul] >= 0x80uy )
    else
    ( s32.[0ul] < 0x80uy ) )

let synth_big_integer_as_octet_string
  (len: asn1_value_int32_of_big_integer)
  (s32: parse_filter_refine (filter_big_integer_as_octet_string len))
: Tot (value: big_integer_as_octet_string_t
               { valid_big_integer_as_octet_string_prop len value })
= let (.[]) = B32.get in
  if (v len = 1) then
  ( (|1ul, s32|) )
  else if (s32.[0ul] = 0x00uy) then
  ( (|len - 1ul, B32.slice s32 1ul len|) )
  else
  ( (|len, s32|) )

val lemma_synth_big_integer_as_octet_string_injective
  (len: asn1_value_int32_of_big_integer)
: Lemma (
  synth_injective (synth_big_integer_as_octet_string len)
)

let synth_big_integer_as_octet_string_inverse
  (len: asn1_value_int32_of_big_integer)
  (value: big_integer_as_octet_string_t {valid_big_integer_as_octet_string_prop len value})
: Tot (s32: parse_filter_refine (filter_big_integer_as_octet_string len)
            { value == synth_big_integer_as_octet_string len s32 })
= let (.[]) = B32.get in
  if len = 1ul then
  ( dsnd value )
  else if (dsnd value).[0ul] >= 0x80uy then
  ( let s32 = B32.create 1ul 0x00uy `B32.append` dsnd value in
    B32.extensionality (dsnd value) (B32.slice s32 1ul len);
    assert (B32.reveal s32 == B32.reveal (B32.create 1ul 0x00uy) `Seq.append` B32.reveal (dsnd value));
    assert (s32.[0ul] = B32.reveal s32 `Seq.index` 0);
    assert (B32.reveal s32 `Seq.index` 0 == B32.create 1ul 0x00uy `B32.get` 0ul);
    assert (B32.create 1ul 0x00uy `B32.get` 0ul == 0x00uy);
    assert (s32.[0ul] == 0x00uy);
    s32 )
  else
  ( dsnd value )

let parse_big_integer_as_octet_string_kind (len: asn1_value_int32_of_big_integer) = constant_size_parser_kind (v len)

noextract
val parse_big_integer_as_octet_string
  (len: asn1_value_int32_of_big_integer)
: parser
    (parse_big_integer_as_octet_string_kind len)
    (x: big_integer_as_octet_string_t {valid_big_integer_as_octet_string_prop len x})

noextract
val serialize_big_integer_as_octet_string
  (len: asn1_value_int32_of_big_integer)
: serializer (parse_big_integer_as_octet_string len)

val lemma_serialize_big_integer_as_octet_string_unfold
  (len: asn1_value_int32_of_big_integer)
  (value: get_parser_type (parse_big_integer_as_octet_string len))
: Lemma (
  serialize (serialize_big_integer_as_octet_string len) value ==
  serialize (serialize_flbytes32 len) (synth_big_integer_as_octet_string_inverse len value))

val lemma_serialize_big_integer_as_octet_string_size
  (len: asn1_value_int32_of_big_integer)
  (value: get_parser_type (parse_big_integer_as_octet_string len))
: Lemma (
  Seq.length (serialize (serialize_big_integer_as_octet_string len) value) == v len)



let parser_tag_of_big_integer_as_octet_string
  (x: big_integer_as_octet_string_t)
: Tot (the_asn1_tag INTEGER & asn1_value_int32_of_big_integer)
= let (.[]) = B32.get in
  if ((dsnd x).[0ul] >= 0x80uy) then
  ( (INTEGER, dfst x + 1ul) )
  else
  ( (INTEGER, dfst x) )

let parse_asn1_length_kind_of_big_integer
= parse_bounded_der_length32_kind 1 (asn1_length_max - 6)

let parse_asn1_length_of_big_integer
: parser parse_asn1_length_kind_of_big_integer asn1_value_int32_of_big_integer
= assert_norm (bounded_int32 1 (asn1_length_max - 6) == asn1_value_int32_of_big_integer);
  _
  `coerce_parser`
  parse_asn1_length_of_bound 1 (asn1_length_max - 6)

let serialize_asn1_length_of_big_integer
: serializer (parse_asn1_length_of_big_integer)
= serialize_asn1_length_of_bound 1 (asn1_length_max - 6)
  `coerce_parser_serializer _`
  (assert_norm (bounded_int32 1 (asn1_length_max - 6) == asn1_value_int32_of_big_integer))

let weak_kind_of_big_integer
= strong_parser_kind 1 (asn1_length_max - 6) None

inline_for_extraction noextract
let parse_big_integer_as_octet_string_TLV_kind
: parser_kind
= parse_asn1_tag_kind
  `and_then_kind`
  parse_asn1_length_kind_of_big_integer
  `and_then_kind`
  weak_kind_of_big_integer

noextract
val parse_big_integer_as_octet_string_TLV
: parser parse_big_integer_as_octet_string_TLV_kind big_integer_as_octet_string_t

noextract
val serialize_big_integer_as_octet_string_TLV
: serializer parse_big_integer_as_octet_string_TLV

val lemma_serialize_big_integer_as_octet_string_TLV_unfold
  (value: big_integer_as_octet_string_t)
: Lemma (
  let tg = parser_tag_of_big_integer_as_octet_string value in
  serialize serialize_big_integer_as_octet_string_TLV value ==
  serialize (serialize_asn1_tag_of_type INTEGER) INTEGER
  `Seq.append`
  serialize (serialize_asn1_length_of_big_integer) (snd tg)
  `Seq.append`
  serialize (serialize_big_integer_as_octet_string (snd tg)) value
)

let len_of_big_integer_as_octet_string_TLV
  (x: big_integer_as_octet_string_t)
: Tot (asn1_TLV_int32_of_big_integer)
= let tg = parser_tag_of_big_integer_as_octet_string x in
  1ul + ASN1.Low.Length.len_of_asn1_length (snd tg) + (snd tg)

val lemma_serialize_big_integer_as_octet_string_TLV_size
  (value: big_integer_as_octet_string_t)
: Lemma (
  Seq.length (serialize serialize_big_integer_as_octet_string_TLV value) ==
  v (len_of_big_integer_as_octet_string_TLV value)
)

let asn1_get_octet_string
  (len: asn1_value_int32_of_type OCTET_STRING)
  (s32: B32.lbytes32 len)
: Tot (datatype_of_asn1_type OCTET_STRING)
= (|len, s32|)

(* Given a big integer in bytes, returns the _encoded_ octet string. *)
let asn1_get_big_integer_as_octet_string
  (len: asn1_value_int32_of_big_integer)
  (s32: B32.lbytes32 len
        { filter_big_integer_as_octet_string len s32 })
: Tot (big_integer_as_octet_string_t)
= synth_big_integer_as_octet_string len s32
