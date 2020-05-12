module ASN1.Base
open FStar.Integers

module B32 = FStar.Bytes

let (.[]) = FStar.Seq.index
let byte = uint_8
let bytes = Seq.seq byte
let lbytes = Seq.Properties.lseq byte

//////////////////////////////////////////////////////////////////////////
/////                           ASN1 Types
/////////////////////////////////////////////////////////////////////////
type asn1_type: Type =
| BOOLEAN
| INTEGER
| NULL
| OCTET_STRING
| BIT_STRING
| OID
| SEQUENCE

/// A specific ASN1 type
inline_for_extraction
let the_asn1_type (a: asn1_type)
: Tot Type
= (a': asn1_type{a == a'})

/// Non constructive ASN1 types
let asn1_primitive_type
= (a: asn1_type{a =!= SEQUENCE})

///////////////////////////////////////////////////////////////////////////
/////      bounded mathematical integers for ASN1 value lengths
///// Defines the valid length/size of a ASN1 DER values
///////////////////////////////////////////////////////////////////////////
let asn1_length_t = n: nat{0 <= n /\ n <= 4294967295}

inline_for_extraction
let asn1_length_min: n: asn1_length_t {forall (n':asn1_length_t). n <= n'} = 0
inline_for_extraction
let asn1_length_max: n: asn1_length_t {forall (n':asn1_length_t). n >= n'} = 4294967295
inline_for_extraction
let asn1_length_inbound (x: nat) (min max: asn1_length_t): bool
= min <= x && x <= max

(* Defining the min and max length of the serialization of ASN1 _value_, not Tag-Len-Value tuples. Note
   that a ASN1 tag always take 1 byte to serialize, a ASN1 length (of value) at most take 5 bytes to
   serialize. Thus the valid length range of ASN1 value's serialization is [asn1_length_min, asn1_length_max - 6].
   Specifically:
   1. BOOLEAN value takes 1 byte;
   2. INTEGER value takes 1-4 bytes (only positive signed integers, see `ASN1.Spec.Value.INTEGER` for details);
   3. NULL value takes 0 bytes;
   4. OCTET_STRING value can take any valid ASN1 value length/size to serialize;
   5. OID is stored as OCTET_STRING;
   6. BIT_STRING value could take arbitrary greater-than-zero valid ASN1 value length/size of bytes, since
      it always take one byte to store the `unused_bits`, see `ASN1.Spec.Value.BIT_STRING` for details;
   7. SEQUENCE value could take arbitrary valid ASN1 value length/size of bytes. *)
inline_for_extraction
let asn1_value_length_min_of_type
  (a: asn1_type)
: asn1_length_t
= match a with
  | BOOLEAN      -> 1                 (* Any `BOOLEAN` value {true, false} has length 1. *)
  | INTEGER      -> 1                 (* `INTEGER` values range in [0x00, 0x7F] has length 1. *)
  | NULL         -> 0                 (* Any `NULL` value has nothing to serialize and has length 0. *)
  | OCTET_STRING -> asn1_length_min   (* An empty `OCTET_STRING` [] has length 0. *)
  | OID          -> asn1_length_min   (* `OID` is just `OCTET_STRING`. *)
  | BIT_STRING   -> 1                 (* An empty `BIT_STRING` with a leading byte of `unused_bits` has length 0. *)
  | SEQUENCE     -> asn1_length_min   (* An empty `SEQUENCE` has length 0. *)

inline_for_extraction
let asn1_value_length_max_of_type
  (a: asn1_type)
: asn1_length_t
= match a with
  | BOOLEAN      -> 1                    (* Any `BOOLEAN` value {true, false} has length 1. *)
  | INTEGER      -> 4                    (* `INTEGER` values range in (0x7FFFFF, 0x7FFFFFFF] has length 4. *)
  | NULL         -> 0                    (* Any `NULL` value has nothing to serialize and has length 0. *)
  | OCTET_STRING -> asn1_length_max - 6  (* An `OCTET_STRING` of size `asn1_length_max - 6`. *)
  | OID          -> asn1_length_max - 6  (* `OID` is just `OCTET_STRING`. *)
  | BIT_STRING   -> asn1_length_max - 6  (* An `BIT_STRING` of size `asn1_length_max - 7` with a leading byte of `unused_bits`. *)
  | SEQUENCE     -> asn1_length_max - 6  (* An `SEQUENCE` whose value has length `asn1_length_max - 6` *)

/// Helper to assert a length `l` is a valid ASN1 value length of the given type `a`
noextract
let asn1_value_length_inbound_of_type
  (a: asn1_type) (l: nat)
: bool
= let min, max = asn1_value_length_min_of_type a, asn1_value_length_max_of_type a in
  asn1_length_inbound l min max

/// Valid ASN1 Value length subtype for a given type`a`
noextract
let asn1_value_length_of_type
  (a: asn1_type)
= l: asn1_length_t {asn1_value_length_inbound_of_type a l}

///////////////////////////////////////////////////////////////////////////
/////      bounded mathematical integers for ASN1 TLV lengths
///// Defines the valid length/size of a ASN1 DER Tag-Length-Value tuple
///////////////////////////////////////////////////////////////////////////

(* NOTE: The valid TLV length range of a ASN1 type is its valid value length
         range plus the corresponding Tag-Length length.
*)
noextract
let asn1_TLV_length_min_of_type
  (a: asn1_type)
: asn1_length_t
= match a with        (* Tag Len Val *)
  | BOOLEAN      -> 3 (*  1 + 1 + 1  *)
  | INTEGER      -> 3 (*  1 + 1 + 1  *)
  | NULL         -> 2 (*  1 + 1 + 0  *)
  | OCTET_STRING -> 2 (*  1 + 1 + 0  *)
  | OID          -> 2 (*  1 + 1 + 0  *)
  | BIT_STRING   -> 3 (*  1 + 1 + 1  *)
  | SEQUENCE     -> 2 (*  1 + 1 + 0  *)

noextract
let asn1_TLV_length_max_of_type
  (a: asn1_type)
: asn1_length_t
= match a with                       (* Tag Len Val *)
  | BOOLEAN      -> 3                (*  1 + 1 + 1  *)
  | INTEGER      -> 6                (*  1 + 1 + 4  *)
  | NULL         -> 2                (*  1 + 1 + 0  *)
  | OCTET_STRING -> asn1_length_max  (*  1 + 5 + _  *)
  | OID          -> asn1_length_max  (*  1 + 5 + _  *)
  | BIT_STRING   -> asn1_length_max  (*  1 + 5 + _  *)
  | SEQUENCE     -> asn1_length_max  (*  1 + 5 + _  *)

/// Helper to assert a length `l` is a valid ASN1 TLV length of the given type `a`
noextract
let asn1_TLV_length_inbound_of_type
  (a: asn1_type) (x: nat)
: bool
= let min, max = asn1_TLV_length_min_of_type a, asn1_TLV_length_max_of_type a in
  asn1_length_inbound x min max

/// Valid ASN1 TLV length subtype for a given type`a`
noextract
let asn1_TLV_length_of_type
  (a: asn1_type)
= l: asn1_length_t {asn1_TLV_length_inbound_of_type a l}



///////////////////////////////////////////////////////////////////////////
/////      bounded machine integers for ASN1 TLV lengths
///// Defines the valid length/size of a ASN1 DER Tag-Length-Value tuple
////  Same as above, specified using the above definitions
///////////////////////////////////////////////////////////////////////////
inline_for_extraction
let asn1_int32 = LowParse.Spec.BoundedInt.bounded_int32 asn1_length_min asn1_length_max
inline_for_extraction
let asn1_int32_min: i: asn1_int32 {forall (i': asn1_int32). i <= i'} = 0ul
inline_for_extraction
let asn1_int32_max: i: asn1_int32 {forall (i': asn1_int32). i >= i'} = 4294967295ul

(* Defining the min and max machine len of the serialization of _value_s *)
inline_for_extraction
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

inline_for_extraction
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

/// Valid ASN1 Value len subtype for a given type`a`
inline_for_extraction
let asn1_value_int32_of_type
  (_a: asn1_type)
= let min, max = asn1_value_length_min_of_type _a, asn1_value_length_max_of_type _a in
  LowParse.Spec.BoundedInt.bounded_int32 min max


///////////////////////////////////////////////////////////////////////////
/////      bounded machine integers for ASN1 TLV lengths
///// Defines the valid length/size of a ASN1 DER Tag-Length-Value tuple
////  Same as the mathematical version above, specified using the above definitions
///////////////////////////////////////////////////////////////////////////
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

/// Valid ASN1 TLV len subtype for a given type`a`
let asn1_TLV_int32_of_type
  (_a: asn1_type)
= let min, max = asn1_TLV_length_min_of_type _a, asn1_TLV_length_max_of_type _a in
  LowParse.Spec.BoundedInt.bounded_int32 min max

//////////////////////////////////////////////////////////////////////
/// A weak parser kind (for ASN1 variable-length values) generator. They
///  generates the strongest _statically_ known parser kind for these types' parser.
///
let weak_kind_of_type
  (a: asn1_type)
: LowParse.Spec.Base.parser_kind
= let min, max = asn1_value_length_min_of_type a, asn1_value_length_max_of_type a in
  LowParse.Spec.Base.strong_parser_kind min max None

////////////////////////////////////////////////////////////////////////
/// OIDs, WIP
type oid_t =
| RIOT_OID
| ECDSA_WITH_SHA256_OID
| KEY_USAGE_OID

type bit_string_t = {
  len        : asn1_value_int32_of_type BIT_STRING;
  unused_bits: n: asn1_int32 {0 <= v n /\ v n <= 7};
  s          : s: B32.bytes { B32.length s == v len - 1 /\
                                             ( if B32.length s = 0 then
                                               ( v unused_bits == 0 )
                                               else
                                               ( let mask: n:nat{cast_ok (Unsigned W8) n} = normalize_term (pow2 (v unused_bits)) in
                                                 let last_byte = B32.index s (B32.length s - 1) in
                                                 0 == normalize_term ((v last_byte) % mask)) )}
}

////////////////////////////////////////////////////////////////////////
////            Representation of ASN1 Values
//// NOTE: They will be directly used in both spec and impl level
////////////////////////////////////////////////////////////////////////
inline_for_extraction
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
  | BIT_STRING   -> bit_string_t

