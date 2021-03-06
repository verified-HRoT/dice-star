module ASN1.Base
open FStar.Integers

module U32 = FStar.UInt32
module B32 = FStar.Bytes

let (.[]) = FStar.Seq.index
let byte = uint_8

inline_for_extraction noextract
let bytes = Seq.seq byte

inline_for_extraction noextract
let lbytes = Seq.Properties.lseq byte

//////////////////////////////////////////////////////////////////////////
/////                           ASN1 Types
/////////////////////////////////////////////////////////////////////////
type asn1_tag_value_t = b: byte {v b <= 0b11111}
type asn1_tag_form_t =
| PRIMITIVE
| CONSTRUCTED
type asn1_tag_class_t =
// (* NOTE: UNIVERSAL is reserved *) | UNIVERSAL
| APPLICATION
| CONTEXT_SPECIFIC
| PRIVATE

type asn1_tag_t: Type =
| BOOLEAN
| INTEGER
| ASN1_NULL
| OCTET_STRING
| PRINTABLE_STRING
| IA5_STRING
| BIT_STRING
| OID
| UTC_TIME
| Generalized_Time
| SEQUENCE
| SET
| CUSTOM_TAG: tag_class: asn1_tag_class_t ->
              tag_form : asn1_tag_form_t  ->
              tag_value: asn1_tag_value_t ->
              asn1_tag_t

type asn1_type = t: asn1_tag_t {not (CUSTOM_TAG? t)}

inline_for_extraction
let the_asn1_tag (a: asn1_tag_t)
: Tot Type
= (a': asn1_tag_t{a == a'})

/// A specific ASN1 type
// inline_for_extraction
// let the_asn1_tag (a: asn1_type)
// : Tot Type
// = (a': asn1_type{a == a'})

/// Non constructive ASN1 types
let asn1_primitive_type
= (a: asn1_type{a =!= SEQUENCE /\ a =!= SET})

let character_string_type : Type
= a: asn1_tag_t { a == IA5_STRING \/ a == PRINTABLE_STRING }

inline_for_extraction noextract
let asn1_implicit_tagging
  (t1 t2: asn1_tag_t)
: asn1_tag_t
= t1

///////////////////////////////////////////////////////////////////////////
/////      bounded mathematical integers for ASN1 value lengths
///// Defines the valid length/size of a ASN1 DER values
///////////////////////////////////////////////////////////////////////////
unfold
let asn1_length_t = nat //{within_bounds (Unsigned W32) n}

inline_for_extraction noextract unfold
let asn1_length_min (*: n: asn1_length_t {forall (n':asn1_length_t). n <= n'}*) = 0
inline_for_extraction noextract unfold
let asn1_length_max (*: n: asn1_length_t {forall (n':asn1_length_t). n >= n'}*) = 4294967295
inline_for_extraction noextract unfold
let asn1_length_inbound (x: nat) (min max: asn1_length_t): bool
= min <= x && x <= max
// unfold
// let asn1_length_inbound_t = n: asn1_length_t { asn1_length_inbound n asn1_length_min asn1_length_max }

(* Defining the min and max length of the serialization of ASN1 _value_, not Tag-Len-Value tuples. Note
   that a ASN1 tag always take 1 byte to serialize, a ASN1 length (of value) at most take 5 bytes to
   serialize. Thus the valid length range of ASN1 value's serialization is [asn1_length_min, asn1_length_max - 6].
   Specifically:
   1. BOOLEAN value takes 1 byte;
   2. INTEGER value takes 1-4 bytes (only positive signed integers, see `ASN1.Spec.Value.INTEGER` for details);
   3. ASN1_NULL value takes 0 bytes;
   4. OCTET_STRING value can take any valid ASN1 value length/size to serialize;
   5. OID is stored as OCTET_STRING;
   6. BIT_STRING value could take arbitrary greater-than-zero valid ASN1 value length/size of bytes, since
      it always take one byte to store the `unused_bits`, see `ASN1.Spec.Value.BIT_STRING` for details;
   7. SEQUENCE value could take arbitrary valid ASN1 value length/size of bytes. *)
inline_for_extraction noextract unfold
[@@ "opaque_to_smt"]
let asn1_value_length_min_of_type
  (a: asn1_tag_t)
: asn1_length_t
= match a with
  | BOOLEAN      -> 1                 (* Any `BOOLEAN` value {true, false} has length 1. *)
  | INTEGER      -> 1                 (* `INTEGER` values range in [0x00, 0x7F] has length 1. *)
  | ASN1_NULL    -> 0                 (* Any `ASN1_NULL` value has nothing to serialize and has length 0. *)
  | OCTET_STRING
  | IA5_STRING
  | PRINTABLE_STRING  -> asn1_length_min   (* An empty `OCTET_STRING` [] has length 0. *)
  | OID          -> asn1_length_min   (* `OID` is just `OCTET_STRING`. *)
  | UTC_TIME -> 13
  | Generalized_Time -> 15
  | BIT_STRING   -> 1                 (* An empty `BIT_STRING` with a leading byte of `unused_bits` has length 0. *)
  | SEQUENCE     -> asn1_length_min   (* An empty `SEQUENCE` has length 0. *)
  | SET          -> asn1_length_min   (* An empty `SET` has length 0. *)
  | CUSTOM_TAG _ _ _ -> asn1_length_min

inline_for_extraction noextract unfold
[@@ "opaque_to_smt"]
let asn1_value_length_max_of_type
  (a: asn1_tag_t)
: asn1_length_t
= match a with
  | BOOLEAN      -> 1                    (* Any `BOOLEAN` value {true, false} has length 1. *)
  | INTEGER      -> 4                    (* `INTEGER` values range in (0x7FFFFF, 0x7FFFFFFF] has length 4. *)
  | ASN1_NULL    -> 0                    (* Any `ASN1_NULL` value has nothing to serialize and has length 0. *)
  | OCTET_STRING
  | IA5_STRING
  | PRINTABLE_STRING -> asn1_length_max - 6  (* An `OCTET_STRING` of size `asn1_length_max - 6`. *)
  | OID          -> asn1_length_max - 6  (* `OID` is just `OCTET_STRING`. *)
  | UTC_TIME -> 13
  | Generalized_Time -> 15
  | BIT_STRING   -> asn1_length_max - 6  (* An `BIT_STRING` of size `asn1_length_max - 7` with a leading byte of `unused_bits`. *)
  | SEQUENCE     -> asn1_length_max - 6  (* An `SEQUENCE` whose value has length `asn1_length_max - 6` *)
  | SET          -> asn1_length_max - 6  (* An `SET` whose value has length `asn1_length_max - 6` *)
  | CUSTOM_TAG _ _ _ -> asn1_length_max - 6

/// Helper to assert a length `l` is a valid ASN1 value length of the given type `a`
noextract unfold
[@@ "opaque_to_smt"]
let asn1_value_length_inbound_of_type
  (a: asn1_tag_t) (l: nat)
: bool
= let min, max = asn1_value_length_min_of_type a, asn1_value_length_max_of_type a in
  asn1_length_inbound l min max

/// Valid ASN1 Value length subtype for a given type`a`
noextract unfold
[@@ "opaque_to_smt"]
let asn1_value_length_of_type
  (a: asn1_tag_t)
= l: asn1_length_t {asn1_value_length_inbound_of_type a l}

///////////////////////////////////////////////////////////////////////////
/////      bounded mathematical integers for ASN1 TLV lengths
///// Defines the valid length/size of a ASN1 DER Tag-Length-Value tuple
///////////////////////////////////////////////////////////////////////////

(* NOTE: The valid TLV length range of a ASN1 type is its valid value length
         range plus the corresponding Tag-Length length.
*)
noextract unfold
[@@ "opaque_to_smt"]
let asn1_TLV_length_min_of_type
  (a: asn1_tag_t)
: asn1_length_t
= match a with        (* Tag Len Val *)
  | BOOLEAN      -> 3 (*  1 + 1 + 1  *)
  | INTEGER      -> 3 (*  1 + 1 + 1  *)
  | ASN1_NULL    -> 2 (*  1 + 1 + 0  *)
  | OCTET_STRING
  | IA5_STRING
  | PRINTABLE_STRING -> 2 (*  1 + 1 + 0  *)
  | OID          -> 2 (*  1 + 1 + 0  *)
  | UTC_TIME -> 15
  | Generalized_Time -> 17
  | BIT_STRING   -> 3 (*  1 + 1 + 1  *)
  | SEQUENCE     -> 2 (*  1 + 1 + 0  *)
  | SET          -> 2 (*  1 + 1 + 0  *)
  | CUSTOM_TAG _ _ _ -> 2

noextract unfold
[@@ "opaque_to_smt"]
let asn1_TLV_length_max_of_type
  (a: asn1_tag_t)
: asn1_length_t
= match a with                       (* Tag Len Val *)
  | BOOLEAN      -> 3                (*  1 + 1 + 1  *)
  | INTEGER      -> 6                (*  1 + 1 + 4  *)
  | ASN1_NULL    -> 2                (*  1 + 1 + 0  *)
  | OCTET_STRING
  | IA5_STRING
  | PRINTABLE_STRING -> asn1_length_max  (*  1 + 5 + _  *)
  | OID          -> asn1_length_max  (*  1 + 5 + _  *)
  | UTC_TIME -> 15
  | Generalized_Time -> 17
  | BIT_STRING   -> asn1_length_max  (*  1 + 5 + _  *)
  | SEQUENCE     -> asn1_length_max  (*  1 + 5 + _  *)
  | SET          -> asn1_length_max  (*  1 + 5 + _  *)
  | CUSTOM_TAG _ _ _ -> asn1_length_max

/// Helper to assert a length `l` is a valid ASN1 TLV length of the given type `a`
noextract unfold
[@@ "opaque_to_smt"]
let asn1_TLV_length_inbound_of_type
  (a: asn1_tag_t) (x: nat)
: bool
= let min, max = asn1_TLV_length_min_of_type a, asn1_TLV_length_max_of_type a in
  asn1_length_inbound x min max

/// Valid ASN1 TLV length subtype for a given type`a`
noextract unfold
[@@ "opaque_to_smt"]
let asn1_TLV_length_of_type
  (a: asn1_tag_t)
= l: asn1_length_t {asn1_TLV_length_inbound_of_type a l}



///////////////////////////////////////////////////////////////////////////
/////      bounded machine integers for ASN1 TLV lengths
///// Defines the valid length/size of a ASN1 DER Tag-Length-Value tuple
////  Same as above, specified using the above definitions
///////////////////////////////////////////////////////////////////////////
unfold
[@@ "opaque_to_smt"]
let asn1_int32_inbounds
  (min: nat)
  (max: nat)
  (x: U32.t)
: GTot bool
= not (U32.v x < min || max < U32.v x)

inline_for_extraction unfold
[@@ "opaque_to_smt"]
// let asn1_int32 = LowParse.Spec.BoundedInt.bounded_int32 asn1_length_min asn1_length_max
let asn1_int32 = n: U32.t { asn1_int32_inbounds asn1_length_min asn1_length_max n }
inline_for_extraction unfold
[@@ "opaque_to_smt"]
let asn1_int32_min: i: asn1_int32 {forall (i': asn1_int32). i <= i'} = 0ul
inline_for_extraction unfold
[@@ "opaque_to_smt"]
let asn1_int32_max: i: asn1_int32 {forall (i': asn1_int32). i >= i'} = 4294967295ul

(* Defining the min and max machine len of the serialization of _value_s *)
inline_for_extraction unfold
[@@ "opaque_to_smt"]
let asn1_value_int32_min_of_type
  (a: asn1_tag_t)
: Tot (n: asn1_int32 {v n == asn1_value_length_min_of_type a})
= match a with
  | BOOLEAN      -> 1ul
  | INTEGER      -> 1ul
  | ASN1_NULL    -> 0ul
  | OCTET_STRING
  | IA5_STRING
  | PRINTABLE_STRING -> asn1_int32_min
  | OID          -> asn1_int32_min
  | UTC_TIME -> 13ul
  | Generalized_Time -> 15ul
  | BIT_STRING   -> 1ul
  | SEQUENCE     -> asn1_int32_min
  | SET          -> asn1_int32_min
  | CUSTOM_TAG _ _ _ -> asn1_int32_min

inline_for_extraction unfold
[@@ "opaque_to_smt"]
let asn1_value_int32_max_of_type
  (a: asn1_tag_t)
: Tot (n: asn1_int32 {v n == asn1_value_length_max_of_type a})
= match a with
  | BOOLEAN      -> 1ul
  | INTEGER      -> 4ul
  | ASN1_NULL    -> 0ul
  | OCTET_STRING
  | IA5_STRING
  | PRINTABLE_STRING -> asn1_int32_max - 6ul
  | OID          -> asn1_int32_max - 6ul
  | UTC_TIME -> 13ul
  | Generalized_Time -> 15ul
  | BIT_STRING   -> asn1_int32_max - 6ul
  | SEQUENCE     -> asn1_int32_max - 6ul
  | SET          -> asn1_int32_max - 6ul
  | CUSTOM_TAG _ _ _ -> asn1_int32_max - 6ul

/// Valid ASN1 Value len subtype for a given type`a`
inline_for_extraction unfold
[@@ "opaque_to_smt"]
let asn1_value_int32_of_type
  (_a: asn1_tag_t)
= [@inline_let]
  let min = asn1_value_length_min_of_type _a in
  [@inline_let]
  let max = asn1_value_length_max_of_type _a in
  // LowParse.Spec.BoundedInt.bounded_int32 min max
  n: U32.t { asn1_int32_inbounds min max n }


///////////////////////////////////////////////////////////////////////////
/////      bounded machine integers for ASN1 TLV lengths
///// Defines the valid length/size of a ASN1 DER Tag-Length-Value tuple
////  Same as the mathematical version above, specified using the above definitions
///////////////////////////////////////////////////////////////////////////
unfold
[@@ "opaque_to_smt"]
let asn1_TLV_int32_min_of_type
  (a: asn1_tag_t)
: Tot (n: asn1_int32 {v n == asn1_TLV_length_min_of_type a})
= match a with
  | BOOLEAN      -> 3ul
  | INTEGER      -> 3ul
  | ASN1_NULL    -> 2ul
  | OCTET_STRING
  | IA5_STRING
  | PRINTABLE_STRING -> 2ul
  | OID          -> 2ul
  | UTC_TIME -> 15ul
  | Generalized_Time -> 17ul
  | BIT_STRING   -> 3ul
  | SEQUENCE     -> 2ul
  | SET          -> 2ul
  | CUSTOM_TAG _ _ _ -> 2ul

unfold
[@@ "opaque_to_smt"]
let asn1_TLV_int32_max_of_type
  (a: asn1_tag_t)
: Tot (n: asn1_int32 {v n == asn1_TLV_length_max_of_type a})
= match a with
  | BOOLEAN      -> 3ul
  | INTEGER      -> 6ul
  | ASN1_NULL    -> 2ul
  | OCTET_STRING
  | IA5_STRING
  | PRINTABLE_STRING -> asn1_int32_max
  | OID          -> asn1_int32_max
  | UTC_TIME -> 15ul
  | Generalized_Time -> 17ul
  | BIT_STRING   -> asn1_int32_max
  | SEQUENCE     -> asn1_int32_max
  | SET          -> asn1_int32_max
  | CUSTOM_TAG _ _ _ -> asn1_int32_max

/// Valid ASN1 TLV len subtype for a given type`a`
unfold
[@@ "opaque_to_smt"]
let asn1_TLV_int32_of_type
  (_a: asn1_tag_t)
= //let min, max = asn1_TLV_length_min_of_type _a, asn1_TLV_length_max_of_type _a in
  // LowParse.Spec.BoundedInt.bounded_int32 min max
  n: asn1_int32 { asn1_int32_inbounds
                    (asn1_TLV_length_min_of_type _a)
                    (asn1_TLV_length_max_of_type _a)
                    n }

//////////////////////////////////////////////////////////////////////
/// A weak parser kind (for ASN1 variable-length values) generator. They
///  generates the strongest _statically_ known parser kind for these types' parser.

///
inline_for_extraction noextract
let weak_kind_of_type
  (a: asn1_tag_t)
: LowParse.Spec.Base.parser_kind
=
  [@inline_let]
  let min = asn1_value_length_min_of_type a in
  [@inline_let]
  let max = asn1_value_length_max_of_type a in
  LowParse.Spec.Base.strong_parser_kind min max None

////////////////////////////////////////////////////////////////////////
/// OIDs, WIP
type oid_t =
| OID_RIOT
| OID_AT_CN
| OID_AT_COUNTRY
| OID_AT_ORGANIZATION
| OID_CLIENT_AUTH
| OID_AUTHORITY_KEY_IDENTIFIER
| OID_KEY_USAGE
| OID_EXTENDED_KEY_USAGE
| OID_BASIC_CONSTRAINTS
// | OID_DIGEST_SHA224
| OID_DIGEST_SHA256
// | OID_DIGEST_SHA384
// | OID_DIGEST_SHA512
| OID_EC_ALG_UNRESTRICTED
| OID_EC_GRP_SECP256R1
| OID_ED25519
| OID_X25519
| OID_PKCS9_CSR_EXT_REQ

#push-options "--z3rlimit 32"
unfold
let valid_bit_string_s_pred
  (len: asn1_value_int32_of_type BIT_STRING)
  (unused_bits: asn1_int32 {0 <= v unused_bits /\ v unused_bits <= 7})
  (s: B32.bytes)
: Type0
= B32.length s == v len - 1 /\
  ( if B32.length s = 0 then
    ( v unused_bits == 0 )
    else
    ( let mask: n:nat{cast_ok (Unsigned W8) n} = (pow2 (v unused_bits)) in
      let last_byte = B32.index s (B32.length s - 1) in
      0 == ((v last_byte) % mask)) )
#pop-options

type bit_string_t = {
  bs_len        : asn1_value_int32_of_type BIT_STRING;
  bs_unused_bits: n: asn1_int32 {0 <= v n /\ v n <= 7};
  bs_s          : s: B32.bytes { valid_bit_string_s_pred bs_len bs_unused_bits s }
}

unfold
let lemma_trivial_bit_string_is_valid
  (len: asn1_value_int32_of_type BIT_STRING)
  (s: B32.lbytes32 (len - 1ul))
: Lemma (
  valid_bit_string_s_pred len 0ul s
)
= ()

let valid_IA5_byte
  (b: byte)
: bool
= b <= 0x7Fuy

let byte_IA5: Type = b: byte { valid_IA5_byte b }
let bytes_IA5 = Seq.seq byte_IA5
let lbytes_IA5 = Seq.lseq byte_IA5

let bytes32_IA5
= s32: B32.bytes
       { forall (i:nat { 0 <= i /\ i < B32.length s32 }). valid_IA5_byte (B32.index s32 i) }

let valid_PRINTABLE_byte
  (b: byte)
: Tot (bool)
= (0x41uy <= b && b <= 0x5Auy) || (* Latin capital letters: A,B, ... Z *)
  (0x61uy <= b && b <= 0x7Auy) || (* Latin small letters: a,b, ... z*)
  (0x30uy <= b && b <= 0x39uy) || (* Numbers: 0,1, ... 9*)
  b = 0x20uy || (* SPACE: (space) *)
  b = 0x27uy || (* APOSTROPHE: ' *)
  b = 0x28uy || (* LEFT PARENTHESIS: ( *)
  b = 0x29uy || (* RIGHT PARENTHESIS: ) *)
  b = 0x2Buy || (* PLUS SIGN: + *)
  b = 0x2Cuy || (* COMMA: , *)
  b = 0x2Duy || (* HYPHEN-MINUS: - *)
  b = 0x2Euy || (* FULL STOP: . *)
  b = 0x2Fuy || (* SOLIDUS: / *)
  b = 0x3Auy || (* COLON: : *)
  b = 0x3Duy || (* EQUALS SIGN: = *)
  b = 0x3Fuy   (* QUESTION MARK: ? *)

let valid_character_string_byte
  (t: character_string_type)
  (b: byte)
: Tot (bool)
= match t with
  | IA5_STRING -> valid_IA5_byte b
  | PRINTABLE_STRING -> valid_PRINTABLE_byte b

let valid_character_string_bytes
  (t: character_string_type)
  (s: bytes)
: Tot (bool)
= Seq.for_all (valid_character_string_byte t) s

noextract
let character_string_list
  (t: character_string_type)
: Type
= l: list byte { valid_character_string_bytes t (Seq.createL l) }

noextract
let character_string_llist
  (t: character_string_type)
  (len: asn1_value_int32_of_type t)
: Type
= l: List.llist byte (v len) { valid_character_string_bytes t (Seq.createL l) }

inline_for_extraction
let character_string_bytes32
  (t: character_string_type)
: Type
= s32: B32.bytes { valid_character_string_bytes t (B32.reveal s32) }

inline_for_extraction
let character_string_lbytes32
  (t: character_string_type)
  (len: asn1_value_int32_of_type t)
: Type
= s32: B32.lbytes32 len { valid_character_string_bytes t (B32.reveal s32) }

// inline_for_extraction
let character_string_t
  (t: character_string_type)
// : Type
= ( len: asn1_value_int32_of_type t &
    character_string_lbytes32 t len)
  
noextract inline_for_extraction
let asn1_utc_time_for_x509_validity_notBefore_default_list
: l: list byte { List.length l == 13 }
= [@inline_let] let l = [0x31uy; 0x37uy; 0x30uy; 0x31uy; 0x30uy; 0x31uy; 0x30uy; 0x30uy; 0x30uy; 0x30uy; 0x30uy; 0x30uy; 0x5Auy] in
  assert_norm (List.length l == 13);
  l

noextract inline_for_extraction
let asn1_utc_time_for_x509_validity_notBefore_default_seq
: s: bytes { Seq.createL_post asn1_utc_time_for_x509_validity_notBefore_default_list s }
= Seq.createL asn1_utc_time_for_x509_validity_notBefore_default_list

let valid_utc_time
  (x: B32.lbytes32 13ul)
: GTot bool
= true

let utc_time_t: Type
= LowParse.Spec.Combinators.parse_filter_refine valid_utc_time

noextract inline_for_extraction
let asn1_generalized_time_for_x509_validity_notAfter_default_list
: l: list byte { List.length l == 15 }
= [@inline_let] let l = [0x39uy; 0x39uy; 0x39uy; 0x39uy; 0x31uy; 0x32uy; 0x33uy; 0x31uy; 0x32uy; 0x33uy; 0x35uy; 0x39uy; 0x35uy; 0x39uy; 0x5Auy] in
  assert_norm (List.length l == 15);
  l

noextract inline_for_extraction
let asn1_generalized_time_for_x509_validity_notAfter_default_seq
: s: bytes { Seq.createL_post asn1_generalized_time_for_x509_validity_notAfter_default_list s }
= Seq.createL asn1_generalized_time_for_x509_validity_notAfter_default_list

// noextract inline_for_extraction
// let x509_validity_notAfter_default_seq
// : s: bytes { Seq.createL_post x509_validity_notAfter_default_list s }
// = Seq.createL x509_validity_notAfter_default_list

let valid_generalized_time
  (x: B32.lbytes32 15ul)
: GTot bool
= x = B32.hide (Seq.createL asn1_generalized_time_for_x509_validity_notAfter_default_list)

let generalized_time_t: Type
= LowParse.Spec.Combinators.parse_filter_refine valid_generalized_time

type octet_string_t = {
  len : asn1_value_int32_of_type OCTET_STRING;
  s  : b:B32.bytes { B32.length b == v len };
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

  | ASN1_NULL    -> unit

  (* An octet string is represented as
     1. `len`: the length of the octet string;
     2. `s`: the octet string. *)
  | OCTET_STRING -> octet_string_t

  | PRINTABLE_STRING
                 -> character_string_t PRINTABLE_STRING

  | IA5_STRING   -> character_string_t IA5_STRING

  | OID          -> oid_t
  
  | UTC_TIME -> utc_time_t

  | Generalized_Time -> generalized_time_t

  (* A bit string is represent as
     1. `len`: the length of both `unused_bits` and `s`;
     2. `unused_bits`: a byte, ranging [0, 7], to represent the number of unused bits in the last byte of `s`.
     3. `s`: bytes, whose last bytes' last `unused_bits` bits should be zeroed. could be an empty bytes. *)
  | BIT_STRING   -> bit_string_t
