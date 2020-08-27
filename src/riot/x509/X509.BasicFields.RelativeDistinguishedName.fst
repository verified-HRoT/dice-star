module X509.BasicFields.RelativeDistinguishedName

open LowParse.Low.Base

open ASN1.Spec
open ASN1.Low

open X509.Base

open FStar.Integers
module B32 = FStar.Bytes

#set-options "--z3rlimit 32 --fuel 0 --ifuel 0"

(*
 *   Name ::= CHOICE { -- only one possibility for now --
 *     rdnSequence  RDNSequence }
 *
 *   RDNSequence ::= SEQUENCE OF RelativeDistinguishedName
 *
 *   RelativeDistinguishedName ::=
 *     SET SIZE (1..MAX) OF AttributeTypeAndValue
 *
 *   AttributeTypeAndValue ::= SEQUENCE {
 *     type     AttributeType,
 *     value    AttributeValue }
 *
 *   AttributeType ::= OBJECT IDENTIFIER
 *
 *   AttributeValue ::= ANY -- DEFINED BY AttributeType
 *
 *   DirectoryString ::= CHOICE {
 *         teletexString           TeletexString (SIZE (1..MAX)),
 *         printableString         PrintableString (SIZE (1..MAX)),
 *         universalString         UniversalString (SIZE (1..MAX)),
 *         utf8String              UTF8String (SIZE (1..MAX)),
 *         bmpString               BMPString (SIZE (1..MAX)) }
 *)

(* TODO: Correct this once other string types are implemented *)
let x509_RDN_attribute_oid: Type
= oid: datatype_of_asn1_type OID
       { oid == OID_AT_CN \/
         oid == OID_AT_COUNTRY \/
         oid == OID_AT_ORGANIZATION }

let directory_string_type : Type
= a: asn1_tag_t { a == IA5_STRING \/ a == PRINTABLE_STRING }

// let directory_string_value
//   (t: directory_string_type)
// = datatype_of_asn1_type t

// type x509_RDN_payload_t =
// | RDN_CN          : t: directory_string_type -> directory_string_value t -> x509_RDN_payload_t
// | RDN_COUNTRY     : t: directory_string_type -> directory_string_value t -> x509_RDN_payload_t
// | RDN_ORGANIZATION: t: directory_string_type -> directory_string_value t -> x509_RDN_payload_t

// #push-options "--fuel 0 --ifuel 1"
// let oid_of_RDN
//   (rdn: x509_RDN_payload_t)
// : Tot (x509_RDN_attribute_oid)
// = match rdn with
//   | RDN_CN           _ _ -> OID_AT_CN
//   | RDN_COUNTRY      _ _ -> OID_AT_COUNTRY
//   | RDN_ORGANIZATION _ _ -> OID_AT_ORGANIZATION

// let asn1_type_of_RDN
//   (rdn: x509_RDN_payload_t)
// : Tot (directory_string_type)
// = match rdn with
//   | RDN_CN           t _ -> t
//   | RDN_COUNTRY      t _ -> t
//   | RDN_ORGANIZATION t _ -> t
// #pop-options

let x509_RDN_payload_t
  (oid: x509_RDN_attribute_oid)
  (t: directory_string_type)
  (lb: asn1_int32)
  (ub: asn1_value_int32_of_type t { lb <= ub })
= (oid `envelop_OID_with_t`
  (asn1_string_with_character_bound_t t (count_character t) lb ub))

let parse_RDN_payload
  (oid: x509_RDN_attribute_oid)
  (t: directory_string_type)
  (lb: asn1_int32)
  (ub: asn1_value_int32_of_type t { lb <= ub })
: parser _ (x509_RDN_payload_t oid t lb ub)
= (oid `parse_envelop_OID_with`
   serialize_asn1_character_string_with_character_bound t lb ub)

let serialize_RDN_payload
  (oid: x509_RDN_attribute_oid)
  (t: directory_string_type)
  (lb: asn1_int32)
  (ub: asn1_value_int32_of_type t { lb <= ub })
: serializer (parse_RDN_payload oid t lb ub)
= (oid `serialize_envelop_OID_with`
   serialize_asn1_character_string_with_character_bound t lb ub)

noextract inline_for_extraction
let serialize32_RDN_payload_backwards
  (oid: x509_RDN_attribute_oid)
  (t: directory_string_type)
  (lb: asn1_int32)
  (ub: asn1_value_int32_of_type t { lb <= ub })
: serializer32_backwards (serialize_RDN_payload oid t lb ub)
= (oid `serialize32_envelop_OID_with_backwards`
   serialize32_asn1_character_string_with_character_bound_backwards t lb ub)

let x509_RDN_t
  (oid: x509_RDN_attribute_oid)
  (t: directory_string_type)
  (lb: asn1_int32)
  (ub: asn1_value_int32_of_type t { lb <= ub })
= SET `inbound_envelop_tag_with_value_of`
  (**) (SEQUENCE `serialize_asn1_envelop_tag_with_TLV`
       (**) (serialize_RDN_payload oid t lb ub))

let parse_RDN
  (oid: x509_RDN_attribute_oid)
  (t: directory_string_type)
  (lb: asn1_int32)
  (ub: asn1_value_int32_of_type t { lb <= ub })
: parser (parse_asn1_envelop_tag_with_TLV_kind (SET)) (x509_RDN_t oid t lb ub)
= (x509_RDN_t oid t lb ub)
  `coerce_parser`
  (SET `parse_asn1_envelop_tag_with_TLV`
  (**) (SEQUENCE `serialize_asn1_envelop_tag_with_TLV`
       (**) (serialize_RDN_payload oid t lb ub)))

let serialize_RDN
  (oid: x509_RDN_attribute_oid)
  (t: directory_string_type)
  (lb: asn1_int32)
  (ub: asn1_value_int32_of_type t { lb <= ub })
: serializer (parse_RDN oid t lb ub)
= coerce_parser_serializer
    (parse_RDN oid t lb ub)
    (SET `serialize_asn1_envelop_tag_with_TLV`
    (**) (SEQUENCE `serialize_asn1_envelop_tag_with_TLV`
       (**) (serialize_RDN_payload oid t lb ub)))
    ()

let valid_RDN_ingredients
  (oid: x509_RDN_attribute_oid)
  (t: directory_string_type)
  (s: datatype_of_asn1_type t)
: Type0
= (length_of_asn1_primitive_TLV #OID oid +
   length_of_asn1_primitive_TLV #t s)
  <= asn1_value_length_max_of_type SEQUENCE /\
  (SEQUENCE `length_of_TLV`
  (**) (length_of_asn1_primitive_TLV #OID oid +
        length_of_asn1_primitive_TLV #t s))
  <= asn1_value_length_max_of_type SET /\
  (SET `length_of_TLV`
  (**) (SEQUENCE `length_of_TLV`
  (**) (length_of_asn1_primitive_TLV #OID oid +
        length_of_asn1_primitive_TLV #t s)))
  <= asn1_TLV_length_max_of_type SET

let length_of_RDN
  (oid: x509_RDN_attribute_oid)
  (t: directory_string_type)
  (s: datatype_of_asn1_type t
      { valid_RDN_ingredients oid t s })
: GTot (asn1_TLV_length_of_type SET)
= (SET `length_of_TLV`
  (**) (SEQUENCE `length_of_TLV`
       (**) (length_of_asn1_primitive_TLV #OID oid +
             length_of_asn1_primitive_TLV #t s)))

noextract inline_for_extraction
let len_of_RDN
  (oid: x509_RDN_attribute_oid)
  (t: directory_string_type)
  (s: datatype_of_asn1_type t
      { valid_RDN_ingredients oid t s })
: Tot (len: asn1_TLV_int32_of_type SET
            { v len == length_of_RDN oid t s })
= (SET `len_of_TLV`
  (**) (SEQUENCE `len_of_TLV`
       (**) (len_of_asn1_primitive_TLV #OID oid +
             len_of_asn1_primitive_TLV #t s)))

let lemma_serialize_RDN_unfold
  (oid: x509_RDN_attribute_oid)
  (t: directory_string_type)
  (lb: asn1_int32)
  (ub: asn1_value_int32_of_type t { lb <= ub })
  (x: x509_RDN_t oid t lb ub)
: Lemma ( predicate_serialize_asn1_envelop_tag_with_TLV_unfold
            (SET)
            (**) (SEQUENCE `serialize_asn1_envelop_tag_with_TLV`
                 (**) (oid `serialize_envelop_OID_with`
                 (**)  serialize_asn1_character_string_with_character_bound t lb ub))
            (x) /\
          predicate_serialize_asn1_envelop_tag_with_TLV_unfold
            (SEQUENCE)
            (**) (oid `serialize_envelop_OID_with`
            (**)  serialize_asn1_character_string_with_character_bound t lb ub)
            (x) /\
          predicate_serialize_envelop_OID_with_unfold
            (oid)
            (serialize_asn1_character_string_with_character_bound t lb ub)
            (x)
            )
= lemma_serialize_asn1_envelop_tag_with_TLV_unfold
    (SET)
    (**) (SEQUENCE `serialize_asn1_envelop_tag_with_TLV`
         (**) (oid `serialize_envelop_OID_with`
         (**)  serialize_asn1_character_string_with_character_bound t lb ub))
    (x);
  lemma_serialize_asn1_envelop_tag_with_TLV_unfold
    (SEQUENCE)
    (**) (oid `serialize_envelop_OID_with`
    (**)  serialize_asn1_character_string_with_character_bound t lb ub)
    (x);
  lemma_serialize_envelop_OID_with_unfold
    (oid)
    (serialize_asn1_character_string_with_character_bound t lb ub)
    (x)

let lemma_serialize_RDN_size
  (oid: x509_RDN_attribute_oid)
  (t: directory_string_type)
  (lb: asn1_int32)
  (ub: asn1_value_int32_of_type t { lb <= ub })
  (x: x509_RDN_t oid t lb ub)
: Lemma ( predicate_serialize_asn1_envelop_tag_with_TLV_size
            (SET)
            (**) (SEQUENCE `serialize_asn1_envelop_tag_with_TLV`
                 (**) (oid `serialize_envelop_OID_with`
                 (**)  serialize_asn1_character_string_with_character_bound t lb ub))
            (x) /\
          predicate_serialize_asn1_envelop_tag_with_TLV_size
            (SEQUENCE)
            (**) (oid `serialize_envelop_OID_with`
            (**)  serialize_asn1_character_string_with_character_bound t lb ub)
            (x) /\
          predicate_serialize_envelop_OID_with_size
            (oid)
            (serialize_asn1_character_string_with_character_bound t lb ub)
            (x)
            )
= lemma_serialize_asn1_envelop_tag_with_TLV_size
    (SET)
    (**) (SEQUENCE `serialize_asn1_envelop_tag_with_TLV`
         (**) (oid `serialize_envelop_OID_with`
         (**)  serialize_asn1_character_string_with_character_bound t lb ub))
    (x);
  lemma_serialize_asn1_envelop_tag_with_TLV_size
    (SEQUENCE)
    (**) (oid `serialize_envelop_OID_with`
    (**)  serialize_asn1_character_string_with_character_bound t lb ub)
    (x);
  lemma_serialize_envelop_OID_with_size
    (oid)
    (serialize_asn1_character_string_with_character_bound t lb ub)
    (x)

let lemma_serialize_RDN_size_exact
  (oid: x509_RDN_attribute_oid)
  (t: directory_string_type)
  (lb: asn1_int32)
  (ub: asn1_value_int32_of_type t { lb <= ub })
  (x: x509_RDN_t oid t lb ub)
: Lemma (
  let x': SEQUENCE `inbound_envelop_tag_with_value_of`
          (oid `serialize_envelop_OID_with`
           serialize_asn1_character_string_with_character_bound t lb ub)
         = (   (coerce_envelop
                 (SET)
                 (SEQUENCE)
                 (oid `serialize_envelop_OID_with`
                  serialize_asn1_character_string_with_character_bound t lb ub)
                 (x))) in
  let s = snd x' in
  let _ = lemma_serialize_RDN_size oid t lb ub x in
  // let _ = lemma_serialize_asn1_oid_TLV_of_size oid oid in
  length_of_opaque_serialization (serialize_RDN oid t lb ub) x <= asn1_TLV_length_max_of_type SET /\
  length_of_opaque_serialization
    (SEQUENCE `serialize_asn1_envelop_tag_with_TLV`
    (**) (oid `serialize_envelop_OID_with`
    (**)  serialize_asn1_character_string_with_character_bound t lb ub))
    (x)
  <= asn1_TLV_length_max_of_type SEQUENCE /\
  // let y = x <: x509_RDN_t oid lb ub t in
  // asn1_value_length_inbound_of_type SET
  // (length_of_opaque_serialization
  //   (SEQUENCE `serialize_asn1_envelop_tag_with_TLV`
  //   (**) (oid `serialize_envelop_OID_with`
  //   (**)  serialize_asn1_character_string_with_character_bound t lb ub))
  //   (x)) /\
  // (length_of_asn1_primitive_TLV #OID oid +
  //  length_of_asn1_primitive_TLV #t s)
  length_of_opaque_serialization
    (oid `serialize_envelop_OID_with`
     serialize_asn1_character_string_with_character_bound t lb ub)
    (x)
  <= asn1_value_length_max_of_type SEQUENCE /\
  length_of_opaque_serialization
    (oid `serialize_envelop_OID_with`
     serialize_asn1_character_string_with_character_bound t lb ub)
    (x)
  == length_of_envelop_OID_with
            (oid)
            (serialize_asn1_character_string_with_character_bound t lb ub)
            (s) /\
  length_of_opaque_serialization (serialize_asn1_character_string_with_character_bound t lb ub) (s)
  == length_of_asn1_primitive_TLV #t s /\
  length_of_opaque_serialization (serialize_asn1_oid_TLV_of oid) oid
  == length_of_asn1_primitive_TLV #OID oid /\
  length_of_opaque_serialization
    (oid `serialize_envelop_OID_with`
     serialize_asn1_character_string_with_character_bound t lb ub)
    (x)
  == (length_of_asn1_primitive_TLV #OID oid +
      length_of_asn1_primitive_TLV #t s) /\
  (SEQUENCE `length_of_TLV`
        (**) (length_of_asn1_primitive_TLV #OID oid +
              length_of_asn1_primitive_TLV #t s))
        <= asn1_TLV_length_max_of_type SEQUENCE /\
  length_of_opaque_serialization (serialize_RDN oid t lb ub) x
  == length_of_RDN oid t s /\
  True
)
= lemma_serialize_RDN_unfold oid t lb ub x;
  lemma_serialize_RDN_size   oid t lb ub x;
  // lemma_serialize_asn1_oid_TLV_of_size oid oid
()

noextract inline_for_extraction
let serialize32_RDN_backwards
  (oid: x509_RDN_attribute_oid)
  (t: directory_string_type)
  (lb: asn1_int32)
  (ub: asn1_value_int32_of_type t { lb <= ub })
= coerce_serializer32_backwards
  (* s2  *) (serialize_RDN oid t lb ub)
  (* s32 *) (SET `serialize32_asn1_envelop_tag_with_TLV_backwards`
            (**) (SEQUENCE `serialize32_asn1_envelop_tag_with_TLV_backwards`
                 (**) (serialize32_RDN_payload_backwards oid t lb ub)))
  (* prf *) ()

(*  *)

type x520_attribute_t =
| COUNTRY
| ORGANIZATION
// | ORGANIZATIONAL_UNIT
// | DISTINGUISHED_NAME_QUALIFIER
// | STATE_OR_PROVINCE_NAME
| COMMON_NAME
// | SERIAL_NUMBER

#push-options "--ifuel 1"
let x520_attribute_lb
  (t: x520_attribute_t)
: Tot (asn1_int32)
= match t with
  | COUNTRY      -> 2ul
  | ORGANIZATION -> 1ul
  | COMMON_NAME  -> 1ul

let x520_attribute_ub
  (t: x520_attribute_t)
: Tot (len: asn1_int32 { len >= x520_attribute_lb t })
= match t with
  | COUNTRY      -> 2ul
  | ORGANIZATION -> 64ul
  | COMMON_NAME  -> 32768ul

let x520_attribute_oid
  (t: x520_attribute_t)
: Tot (datatype_of_asn1_type OID)
= match t with
  | COUNTRY      -> OID_AT_COUNTRY
  | ORGANIZATION -> OID_AT_ORGANIZATION
  | COMMON_NAME  -> OID_AT_CN

let x509_RDN_x520_attribute_t
  (t: x520_attribute_t)
  (string_t: directory_string_type { ((t == COUNTRY) ==> (string_t == PRINTABLE_STRING)) })
= x509_RDN_t
    (x520_attribute_oid t)
    (string_t)
    (x520_attribute_lb t)
    (x520_attribute_ub t)

noextract inline_for_extraction
let x509_RDN_x520_attribute_string_t
  (t: x520_attribute_t)
  (string_t: directory_string_type { ((t == COUNTRY) ==> (string_t == PRINTABLE_STRING)) })
// = get_parser_type (parse_asn1_character_string_with_character_bound string_t (x520_attribute_lb t) (x520_attribute_ub t))
= asn1_string_with_character_bound_t
    (string_t)
    (count_character string_t)
    (x520_attribute_lb t)
    (x520_attribute_ub t)

let lemma_RDN_x520_attribute_size
  (#t: x520_attribute_t)
  (#string_t: directory_string_type { ((t == COUNTRY) ==> (string_t == PRINTABLE_STRING)) })
  (s: x509_RDN_x520_attribute_string_t t string_t)
: Lemma (
  asn1_value_length_inbound_of_type
    (string_t)
    (length_of_opaque_serialization (serialize_asn1_TLV_of_type string_t) s) /\
  asn1_value_length_inbound_of_type
    (SEQUENCE)
    (length_of_opaque_serialization ((x520_attribute_oid t) `serialize_envelop_OID_with`
                                     (serialize_asn1_TLV_of_type string_t))
                                    ((x520_attribute_oid t), s)) /\
  (serialize_asn1_character_string_with_character_bound
      (string_t)
      (x520_attribute_lb t)
      (x520_attribute_ub t)) `serialize` s
  == serialize_asn1_TLV_of_type string_t `serialize` s
)
= lemma_serialize_character_string_size string_t s;
  lemma_serialize_asn1_oid_TLV_of_size (x520_attribute_oid t) (x520_attribute_oid t);
  lemma_serialize_envelop_OID_with_size
    (x520_attribute_oid t)
    (serialize_asn1_TLV_of_type string_t)
    ((x520_attribute_oid t), s)

let parse_RDN_x520_attribute
  (t: x520_attribute_t)
  (string_t: directory_string_type { ((t == COUNTRY) ==> (string_t == PRINTABLE_STRING)) })
: parser (parse_asn1_envelop_tag_with_TLV_kind (SET)) (x509_RDN_x520_attribute_t t string_t)
= (x509_RDN_x520_attribute_t t string_t)
  `coerce_parser`
  (parse_RDN (x520_attribute_oid t) (string_t) (x520_attribute_lb t) (x520_attribute_ub t))

let serialize_RDN_x520_attribute
  (t: x520_attribute_t)
  (string_t: directory_string_type { ((t == COUNTRY) ==> (string_t == PRINTABLE_STRING)) })
: serializer (parse_RDN_x520_attribute t string_t)
= coerce_parser_serializer
    (parse_RDN_x520_attribute t string_t)
    (serialize_RDN (x520_attribute_oid t) (string_t) (x520_attribute_lb t) (x520_attribute_ub t))
    ()

let length_of_RDN_x520_attribute
  (#t: x520_attribute_t)
  (#string_t: directory_string_type { ((t == COUNTRY) ==> (string_t == PRINTABLE_STRING)) })
  (s: x509_RDN_x520_attribute_string_t t string_t)
: GTot (asn1_TLV_length_of_type SET)
= length_of_RDN
    (x520_attribute_oid t)
    (string_t)
    (s)

noextract inline_for_extraction
let len_of_RDN_x520_attribute
  (#t: x520_attribute_t)
  (#string_t: directory_string_type { ((t == COUNTRY) ==> (string_t == PRINTABLE_STRING)) })
  (s: x509_RDN_x520_attribute_string_t t string_t)
: Tot (len: asn1_TLV_int32_of_type SET
            { v len == length_of_RDN_x520_attribute s })
= len_of_RDN
    (x520_attribute_oid t)
    (string_t)
    (s)

noextract inline_for_extraction
let get_RDN_x520_attribute_string
  (#t: x520_attribute_t)
  (#string_t: directory_string_type { ((t == COUNTRY) ==> (string_t == PRINTABLE_STRING)) })
  (x: x509_RDN_x520_attribute_t t string_t)
: Tot (x509_RDN_x520_attribute_string_t t string_t)
= snd (coerce_envelop
        (SET)
        (SEQUENCE)
        ((x520_attribute_oid t) `serialize_envelop_OID_with`
          serialize_asn1_character_string_with_character_bound string_t (x520_attribute_lb t) (x520_attribute_ub t))
        (x))

let lemma_serialize_RDN_x520_attribute_unfold
  (#t: x520_attribute_t)
  (#string_t: directory_string_type { ((t == COUNTRY) ==> (string_t == PRINTABLE_STRING)) })
  (x: x509_RDN_x520_attribute_t t string_t)
= lemma_serialize_RDN_unfold (x520_attribute_oid t) (string_t) (x520_attribute_lb t) (x520_attribute_ub t) x

let lemma_serialize_RDN_x520_attribute_size
  (#t: x520_attribute_t)
  (#string_t: directory_string_type { ((t == COUNTRY) ==> (string_t == PRINTABLE_STRING)) })
  (x: x509_RDN_x520_attribute_t t string_t)
= lemma_serialize_RDN_size (x520_attribute_oid t) (string_t) (x520_attribute_lb t) (x520_attribute_ub t) x

#push-options "--z3rlimit 64"
let lemma_serialize_RDN_x520_attribute_size_exact
  (#t: x520_attribute_t)
  (#string_t: directory_string_type { ((t == COUNTRY) ==> (string_t == PRINTABLE_STRING)) })
  (x: x509_RDN_x520_attribute_t t string_t)
: Lemma (
  length_of_opaque_serialization (serialize_RDN_x520_attribute _ _) x
  == length_of_RDN_x520_attribute (get_RDN_x520_attribute_string x)
)
= lemma_serialize_RDN_size_exact (x520_attribute_oid t) (string_t) (x520_attribute_lb t) (x520_attribute_ub t) x
#pop-options

noextract inline_for_extraction
let serialize32_RDN_x520_attribute_backwards
  (t: x520_attribute_t)
  (string_t: directory_string_type { ((t == COUNTRY) ==> (string_t == PRINTABLE_STRING)) })
: serializer32_backwards (serialize_RDN_x520_attribute t string_t)
= coerce_serializer32_backwards
    (serialize_RDN_x520_attribute t string_t)
    (serialize32_RDN_backwards (x520_attribute_oid t) (string_t) (x520_attribute_lb t) (x520_attribute_ub t))
    ()

// #push-options "--fuel 4 --ifuel 0"
// let _ = assert_norm (Seq.for_all valid_IA5_byte (B32.reveal (B32.hide (Seq.createL [0x10uy; 0x11uy; 0x12uy]))) )

// let x: x509_RDN_x520_attribute_string_t COMMON_NAME IA5_STRING
// = assert_norm (Seq.for_all valid_IA5_byte (B32.reveal (B32.hide (Seq.createL [0x10uy; 0x11uy; 0x12uy]))));
//   (|3ul, B32.hide (Seq.createL [0x10uy; 0x11uy; 0x12uy])|) <: datatype_of_asn1_type IA5_STRING

// #push-options "--max_fuel 4 --max_ifuel 4"
noextract inline_for_extraction
let asn1_get_character_string
  (#string_t: character_string_type)
  (len: asn1_value_int32_of_type string_t)
  (s32: character_string_lbytes32 string_t len)
: Tot (datatype_of_asn1_type string_t)
= (|len, s32|) <: character_string_t string_t

noextract inline_for_extraction
let x509_get_RDN_x520_attribute_string
  (#t: x520_attribute_t)
  (#string_t: directory_string_type { ((t == COUNTRY) ==> (string_t == PRINTABLE_STRING)) })
  (x: parse_filter_refine (filter_asn1_string_with_character_bound string_t
                            (count_character string_t)
                            (x520_attribute_lb t)
                            (x520_attribute_ub t)))
: Tot (x509_RDN_x520_attribute_string_t t string_t)
= x

#push-options "--z3rlimit 96"
noextract inline_for_extraction
let x509_get_RDN_x520_attribute
  (#t: x520_attribute_t)
  (#string_t: directory_string_type { ((t == COUNTRY) ==> (string_t == PRINTABLE_STRING)) })
  (x: x509_RDN_x520_attribute_string_t t string_t)
: Tot (x509_RDN_x520_attribute_t t string_t)
=
  let attr: (x520_attribute_oid t) `envelop_OID_with_t`
            (x509_RDN_x520_attribute_string_t t string_t) = (
      x520_attribute_oid t,
      x
  ) in
  (* Prf *) lemma_serialize_asn1_oid_TLV_of_size (x520_attribute_oid t) (x520_attribute_oid t);
  (* Prf *) lemma_serialize_character_string_size string_t x;
  (* Prf *) lemma_serialize_envelop_OID_with_size
              (x520_attribute_oid t)
              (serialize_asn1_character_string_with_character_bound
                (string_t)
                (x520_attribute_lb t)
                (x520_attribute_ub t))
              (attr);
  (* Prf *) lemma_serialize_asn1_sequence_TLV_size
              ((x520_attribute_oid t) `serialize_envelop_OID_with`
               (serialize_asn1_character_string_with_character_bound
                (string_t)
                (x520_attribute_lb t)
                (x520_attribute_ub t)))
              (attr);
(* return *) (attr)
#pop-options

(*
 *
 *)
(*)
let x509_name_pair_t
: Type = ( name: x520_attribute_t & t:directory_string_type { (name == COUNTRY) ==> (t == PRINTABLE_STRING) } )

let valid_x520_attribute_list
  (l: list x509_name_pair_t)
: Type0
= 0 < List.length l

(* SHOULD BE PARTIAL EVALUATED OUT *)
let x520_attribute_list_t
: Type
= l: list x509_name_pair_t { valid_x520_attribute_list l }

#set-options "--fuel 2 --ifuel 2"

let rec x509_name_t
  (l: x520_attribute_list_t)
: Tot (Type)
  (decreases (List.length l))
= match l with
  | hd :: [] -> let name = dfst hd in
               let t: t: _ { (name == COUNTRY) ==> (t == PRINTABLE_STRING) } = dsnd hd in
               get_parser_type (parse_RDN_x520_attribute name t) //t: x520_attribute_t { t == dfst hd }
  | hd :: tl -> let name = dfst hd in
               let t: t: _ { (name == COUNTRY) ==> (t == PRINTABLE_STRING) } = dsnd hd in
               (get_parser_type (parse_RDN_x520_attribute name t)) `tuple2` (x509_name_t tl)

let rec parse_x509_name_kind
  (l: x520_attribute_list_t)
: Tot (parser_kind)
  (decreases (List.length l))
= match l with
  | hd :: [] -> let name = dfst hd in
               let t: t: _ { (name == COUNTRY) ==> (t == PRINTABLE_STRING) } = dsnd hd in
               get_parser_kind (parse_RDN_x520_attribute name t)
  | hd :: tl -> let name = dfst hd in
               let t: t: _ { (name == COUNTRY) ==> (t == PRINTABLE_STRING) } = dsnd hd in
               (get_parser_kind (parse_RDN_x520_attribute name t)) `and_then_kind` (parse_x509_name_kind tl)

let rec parse_x509_name
  (l: x520_attribute_list_t)
: Tot (parser (parse_x509_name_kind l) (x509_name_t l))
  (decreases (List.length l))
= match l with
  | hd :: [] -> admit();let name = dfst hd in
               let t: t: _ { (name == COUNTRY) ==> (t == PRINTABLE_STRING) } = dsnd hd in
               parse_RDN_x520_attribute name t
  | hd :: tl -> admit();
               let name = dfst hd in
               let t: t: _ { (name == COUNTRY) ==> (t == PRINTABLE_STRING) } = dsnd hd in
               (parse_RDN_x520_attribute name t) `nondep_then` (parse_x509_name tl)

(* 1. option; 2. choice; 3. default; 4. list *)

// let x509_name_t

(*)
let serialize32_RDN_backwards
  (oid: x509_RDN_attribute_oid)
  (t: directory_string_type)
  (lb: asn1_int32)
  (ub: asn1_value_int32_of_type t { lb <= ub })
: serializer32_backwards (serialize_RDN oid t lb ub)
= coerce_serializer32_backwards
    (serialize_RDN oid t)
    (SET `serialize32_asn1_envelop_tag_with_TLV_backwards`
    (**) (SEQUENCE `serialize32_asn1_envelop_tag_with_TLV_backwards`
         (**) (oid `serialize32_envelop_OID_with_backwards`
         (**)  serialize32_asn1_TLV_backwards_of_type t)))
    ()

(*
 *   Standard sets of attributes have been defined in the X.500 series of
 *   specifications [X.520].  Implementations of this specification MUST
 *   be prepared to receive the following standard attribute types in
 *   issuer and subject (Section 4.1.2.6) names:
 *
 *      * country,
 *      * organization,
 *      * organizational unit,
 *      * distinguished name qualifier,
 *      * state or province name,
 *      * common name (e.g., "Susan Housley"), and
 *      * serial number.
 *
 *   In addition, implementations of this specification SHOULD be prepared
 *   to receive the following standard attribute types in issuer and
 *   subject names:
 *
 *      * locality,
 *      * title,
 *      * surname,
 *      * given name,
 *      * initials,
 *      * pseudonym, and
 *      * generation qualifier (e.g., "Jr.", "3rd", or "IV").
 *
 *   The syntax and associated object identifiers (OIDs) for these
 *   attribute types are provided in the ASN.1 modules in Appendix A.
 *)

(*
 * -- Upper Bounds
 * ub-name INTEGER ::= 32768
 * ub-common-name INTEGER ::= 64
 * ub-locality-name INTEGER ::= 128
 * ub-state-name INTEGER ::= 128
 * ub-organization-name INTEGER ::= 64
 * ub-organizational-unit-name INTEGER ::= 64
 * ub-title INTEGER ::= 64
 * ub-serial-number INTEGER ::= 64
 * ub-match INTEGER ::= 128
 * ub-emailaddress-length INTEGER ::= 255
 * ub-common-name-length INTEGER ::= 64
 * ub-country-name-alpha-length INTEGER ::= 2
 * ub-country-name-numeric-length INTEGER ::= 3
 * ub-domain-defined-attributes INTEGER ::= 4
 * ub-domain-defined-attribute-type-length INTEGER ::= 8
 * ub-domain-defined-attribute-value-length INTEGER ::= 128
 * ub-domain-name-length INTEGER ::= 16
 * ub-extension-attributes INTEGER ::= 256
 * ub-e163-4-number-length INTEGER ::= 15
 * ub-e163-4-sub-address-length INTEGER ::= 40
 * ub-generation-qualifier-length INTEGER ::= 3
 * ub-given-name-length INTEGER ::= 16
 * ub-initials-length INTEGER ::= 5
 * ub-integer-options INTEGER ::= 256
 * ub-numeric-user-id-length INTEGER ::= 32
 * ub-organization-name-length INTEGER ::= 64
 * ub-organizational-unit-name-length INTEGER ::= 32
 * ub-organizational-units INTEGER ::= 4
 * ub-pds-name-length INTEGER ::= 16
 * ub-pds-parameter-length INTEGER ::= 30
 * ub-pds-physical-address-lines INTEGER ::= 6
 * ub-postal-code-length INTEGER ::= 16
 * ub-pseudonym INTEGER ::= 128
 * ub-surname-length INTEGER ::= 40
 * ub-terminal-id-length INTEGER ::= 24
 * ub-unformatted-address-length INTEGER ::= 180
 * ub-x121-address-length INTEGER ::= 16
 *
 * -- Note - upper bounds on string types, such as TeletexString, are
 * -- measured in characters.  Excepting PrintableString or IA5String, a
 * -- significantly greater number of octets will be required to hold
 * -- such a value.  As a minimum, 16 octets, or twice the specified
 * -- upper bound, whichever is the larger, should be allowed for
 * -- TeletexString.  For UTF8String or UniversalString at least four
 * -- times the upper bound should be allowed.
 *)

