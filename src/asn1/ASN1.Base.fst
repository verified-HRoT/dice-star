module ASN1.Base
open FStar.Integers

module B32 = FStar.Bytes

let (.[]) = FStar.Seq.index
let byte = uint_8
let bytes = Seq.seq byte
let lbytes = Seq.Properties.lseq byte

/// ASN1 Types
///
type asn1_type: Type =
| BOOLEAN
| INTEGER
| NULL
| OCTET_STRING
| BIT_STRING
| OID
| SEQUENCE

let the_asn1_type (a: asn1_type)
: Tot Type
= (a': asn1_type{a == a'})

let asn1_primitive_type
= (a: asn1_type{a =!= SEQUENCE})


///////////////////////////////////////////////////////////////////////////
/// ASN1 bounded mathematical integers
///
noextract
let asn1_length_t = n: nat{0 <= n /\ n <= 4294967295}
noextract
let asn1_length_min: n: asn1_length_t {forall (n':asn1_length_t). n <= n'} = 0
noextract
let asn1_length_max: n: asn1_length_t {forall (n':asn1_length_t). n >= n'} = 4294967295
noextract
let asn1_length_inbound (x: nat) (min max: asn1_length_t): bool
= min <= x && x <= max

(* Defining the min and max length of the serialization of _value_s, not tag-len-value tuples.
   1. BOOLEAN value takes 1 byte;
   2. INTEGER value takes 1-4 bytes (positive signed integers, see `ASN1.Spec.INTEGER` for details);
   3. NULL value takes 0 bytes;
   4. OCTET_STRING value could take arbitrary valid length/size of bytes;
   5. OID is stored as OCTET_STRING, thus it could also take arbitrary valid length/size of bytes;
   6. BIT_STRING value could take arbitrary greater-than-zero valid length/size of bytes, since it
      always take one byte to store the `unused_bits`, see `ASN1.Spec.BIT_STRING` for details;
   7. SEQUENCE value could take arbitrary valid length/size of bytes.
NOTE: Making the max length be `ans1_length_max - 6` to make all TLV be inbound (Tag takes 1 byte and
      Len takes at most 5 bytes).
*)
(* NOTE: Not marking them with `GTot` because many definition's total definitions need them. *)
noextract
let asn1_value_length_min_of_type
  (a: asn1_type)
: asn1_length_t
= match a with
  | BOOLEAN      -> 1
  | INTEGER      -> 1
  | NULL         -> 0
  | OCTET_STRING -> asn1_length_min
  | OID          -> asn1_length_min
  | BIT_STRING   -> 1
  | SEQUENCE     -> asn1_length_min

noextract
let asn1_value_length_max_of_type
  (a: asn1_type)
: asn1_length_t
= match a with
  | BOOLEAN      -> 1
  | INTEGER      -> 4
  | NULL         -> 0
  | OCTET_STRING -> asn1_length_max - 6
  | OID          -> asn1_length_max - 6
  | BIT_STRING   -> asn1_length_max - 6
  | SEQUENCE     -> asn1_length_max - 6

noextract
let asn1_value_length_bound_of_type
  (a: asn1_type)
: (asn1_length_t & asn1_length_t)
= (asn1_value_length_min_of_type a, asn1_value_length_max_of_type a)

noextract
let asn1_value_length_inbound_of_type
  (a: asn1_type) (x: nat)
: bool
= let min, max = asn1_value_length_bound_of_type a in
  asn1_length_inbound x min max

/// Valid mathematical integer for a specific type
noextract
let asn1_value_length_of_type
  (a: asn1_type)
= l: asn1_length_t {asn1_value_length_inbound_of_type a l}

//////////////////////////////////////////////////////////////
noextract
let asn1_TLV_length_min_of_type
  (a: asn1_type)
: asn1_length_t
= match a with
  | BOOLEAN      -> 3
  | INTEGER      -> 3
  | NULL         -> 2
  | OCTET_STRING -> 2
  | OID          -> 2
  | BIT_STRING   -> 3
  | SEQUENCE     -> 2

noextract
let asn1_TLV_length_max_of_type
  (a: asn1_type)
: asn1_length_t
= match a with
  | BOOLEAN      -> 3
  | INTEGER      -> 6
  | NULL         -> 2
  | OCTET_STRING -> asn1_length_max
  | OID          -> asn1_length_max
  | BIT_STRING   -> asn1_length_max
  | SEQUENCE     -> asn1_length_max

noextract
let asn1_TLV_length_bound_of_type
  (a: asn1_type)
: (asn1_length_t & asn1_length_t)
= (asn1_TLV_length_min_of_type a, asn1_TLV_length_max_of_type a)

noextract
let asn1_TLV_length_inbound_of_type
  (a: asn1_type) (x: nat)
: bool
= let min, max = asn1_TLV_length_bound_of_type a in
  asn1_length_inbound x min max

/// Valid mathematical integer for a specific type
noextract
let asn1_TLV_length_of_type
  (a: asn1_type)
= l: asn1_length_t {asn1_TLV_length_inbound_of_type a l}

//////////////////////////////////////////////////////////////
/// ASN1 bounded 32-bit unsigned machine integers
///
let asn1_int32 = LowParse.Spec.BoundedInt.bounded_int32 asn1_length_min asn1_length_max
let asn1_int32_min: i: asn1_int32 {forall (i': asn1_int32). i <= i'} = 0ul
let asn1_int32_max: i: asn1_int32 {forall (i': asn1_int32). i >= i'} = 4294967295ul

(* Defining the min and max machine len of the serialization of _value_s *)
let asn1_value_int32_min_of_type
  (a: asn1_type)
: Tot (n: asn1_int32 {v n == asn1_value_length_min_of_type a})
= match a with
  | BOOLEAN      -> 1ul
  | INTEGER      -> 1ul
  | NULL         -> 0ul
  | OCTET_STRING -> asn1_int32_min
  | OID          -> asn1_int32_min
  | BIT_STRING   -> 1ul
  | SEQUENCE     -> asn1_int32_min

let asn1_value_int32_max_of_type
  (a: asn1_type)
: Tot (n: asn1_int32 {v n == asn1_value_length_max_of_type a})
= match a with
  | BOOLEAN      -> 1ul
  | INTEGER      -> 4ul
  | NULL         -> 0ul
  | OCTET_STRING -> asn1_int32_max - 6ul
  | OID          -> asn1_int32_max - 6ul
  | BIT_STRING   -> asn1_int32_max - 6ul
  | SEQUENCE     -> asn1_int32_max - 6ul

let asn1_value_int32_bound_of_type
  (a: asn1_type)
: Tot (x: (asn1_int32 & asn1_int32) {
          let (vmin, vmax) = asn1_value_length_bound_of_type a in
          let (min , max ) = x in
          v min == vmin /\ v max == vmax })
= (asn1_value_int32_min_of_type a, asn1_value_int32_max_of_type a)

/// Valid mathematical integer for a specific type
let asn1_value_int32_of_type
  (_a: asn1_type)
= let min, max = asn1_value_length_min_of_type _a, asn1_value_length_max_of_type _a in
  LowParse.Spec.BoundedInt.bounded_int32 min max

/////////////////////////////////////////////////////////////////////////////////
let asn1_TLV_int32_min_of_type
  (a: asn1_type)
: Tot (n: asn1_int32 {v n == asn1_TLV_length_min_of_type a})
= match a with
  | BOOLEAN      -> 3ul
  | INTEGER      -> 3ul
  | NULL         -> 2ul
  | OCTET_STRING -> 2ul
  | OID          -> 2ul
  | BIT_STRING   -> 3ul
  | SEQUENCE     -> 2ul

let asn1_TLV_int32_max_of_type
  (a: asn1_type)
: Tot (n: asn1_int32 {v n == asn1_TLV_length_max_of_type a})
= match a with
  | BOOLEAN      -> 3ul
  | INTEGER      -> 6ul
  | NULL         -> 2ul
  | OCTET_STRING -> asn1_int32_max
  | OID          -> asn1_int32_max
  | BIT_STRING   -> asn1_int32_max
  | SEQUENCE     -> asn1_int32_max

let asn1_TLV_int32_bound_of_type
  (a: asn1_type)
: Tot (x: (asn1_int32 & asn1_int32) {
          let (vmin, vmax) = asn1_TLV_length_bound_of_type a in
          let (min , max ) = x in
          v min == vmin /\ v max == vmax })
= (asn1_TLV_int32_min_of_type a, asn1_TLV_int32_max_of_type a)

/// Valid mathematical integer for a specific type
let asn1_TLV_int32_of_type
  (_a: asn1_type)
= let min, max = asn1_TLV_length_min_of_type _a, asn1_TLV_length_max_of_type _a in
  LowParse.Spec.BoundedInt.bounded_int32 min max

//////////////////////////////////////////////////////////////////////
/// A weak parser kind generator. They generates the strongest (I hope)
/// _statically_ known parser kind for these types' parser.
///
let weak_kind_of_type
  (a: asn1_type)
: LowParse.Spec.Base.parser_kind
= let min, max = asn1_value_length_bound_of_type a in
  LowParse.Spec.Base.strong_parser_kind min max None


////////////////////////////////////////////////////////////////////////
/// OIDs, WIP
type oid_t =
| RIOT_OID
| ECDSA_WITH_SHA256_OID
| KEY_USAGE_OID


////////////////////////////////////////////////////////////////////////
/// The representation of the value of asn1 types. They will also be used
/// at the low-level.
/// NOTE: Not inductively defining them.
/// NOTE: Currently using dependent tuples. We can also switch to records.
///
let datatype_of_asn1_type (a: asn1_primitive_type): Type
= match a with
  | BOOLEAN      -> bool

  (* Positive 32-bit _signed_ integer. *)
  | INTEGER      -> ( i: int_32{v i >= 0} )

  | NULL         -> unit

  (* An octet string is represented as
     1. `len`: the length of the octet string;
     2. `s`: the octet string. *)
  | OCTET_STRING -> ( len: asn1_value_int32_of_type OCTET_STRING &
                      s  : B32.bytes { B32.length s == v len } )

  (* WIP *)
  | OID          -> oid_t

  (* A bit string is represent as
     1. `len`: the length of both `unused_bits` and `s`;
     2. `unused_bits`: a byte, ranging [0, 7], to represent the number of unused bits in the last byte of `s`.
     3. `s`: bytes, whose last bytes' last `unused_bits` bits should be zeroed. could be an empty bytes. *)
  | BIT_STRING   -> ( len        : asn1_value_int32_of_type BIT_STRING &
                      unused_bits: asn1_int32 {0 <= v unused_bits /\ v unused_bits <= 7} &
                      s          : B32.bytes { B32.length s == v len - 1 /\
                                             ( if B32.length s = 0 then
                                               ( v unused_bits == 0 )
                                               else
                                               ( let mask: n:nat{cast_ok (Unsigned W8) n} = normalize_term (pow2 (v unused_bits)) in
                                                 let last_byte = B32.index s (B32.length s - 1) in
                                                 0 == normalize_term ((v last_byte) % mask)) )} )

