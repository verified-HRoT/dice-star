module X509.BasicFields.RelativeDistinguishedName2

open LowParse.Low.Base

open ASN1.Spec
open ASN1.Low

open X509.Base

open FStar.Integers
module B32 = FStar.Bytes

#set-options "--z3rlimit 32 --fuel 0 --ifuel 0"

let x509_RDN_attribute_oid: Type
= oid: datatype_of_asn1_type OID
       { oid == OID_AT_CN \/
         oid == OID_AT_COUNTRY \/
         oid == OID_AT_ORGANIZATION }

let directory_string_type : Type
= a: asn1_tag_t { a == IA5_STRING \/ a == PRINTABLE_STRING }

(* Payload *)

inline_for_extraction
let x509_RDN_payload_t
  (oid: x509_RDN_attribute_oid)
  (t: directory_string_type)
  (lb: asn1_int32)
  (ub: asn1_value_int32_of_type t { lb <= ub })
= (oid `envelop_OID_with_t`
  (asn1_string_with_character_bound_t t (count_character t) lb ub))

val parse_RDN_payload
  (oid: x509_RDN_attribute_oid)
  (t: directory_string_type)
  (lb: asn1_int32)
  (ub: asn1_value_int32_of_type t { lb <= ub })
: parser
  (and_then_kind
    (parse_filter_kind parse_asn1_oid_TLV_kind)
    (parse_asn1_string_TLV_kind t))
  (x509_RDN_payload_t oid t lb ub)

val serialize_RDN_payload
  (oid: x509_RDN_attribute_oid)
  (t: directory_string_type)
  (lb: asn1_int32)
  (ub: asn1_value_int32_of_type t { lb <= ub })
: serializer (parse_RDN_payload oid t lb ub)

noextract inline_for_extraction
val serialize32_RDN_payload_backwards
  (oid: x509_RDN_attribute_oid)
  (t: directory_string_type)
  (lb: asn1_int32)
  (ub: asn1_value_int32_of_type t { lb <= ub })
: serializer32_backwards (serialize_RDN_payload oid t lb ub)

(* RDN *)
inline_for_extraction
let x509_RDN_t
  (oid: x509_RDN_attribute_oid)
  (t: directory_string_type)
  (lb: asn1_int32)
  (ub: asn1_value_int32_of_type t { lb <= ub })
= SET `inbound_envelop_tag_with_value_of`
  (**) (SEQUENCE `serialize_asn1_envelop_tag_with_TLV`
       (**) (serialize_RDN_payload oid t lb ub))

val parse_RDN
  (oid: x509_RDN_attribute_oid)
  (t: directory_string_type)
  (lb: asn1_int32)
  (ub: asn1_value_int32_of_type t { lb <= ub })
: parser (parse_asn1_envelop_tag_with_TLV_kind (SET)) (x509_RDN_t oid t lb ub)

val serialize_RDN
  (oid: x509_RDN_attribute_oid)
  (t: directory_string_type)
  (lb: asn1_int32)
  (ub: asn1_value_int32_of_type t { lb <= ub })
: serializer (parse_RDN oid t lb ub)

noextract inline_for_extraction
val serialize32_RDN_backwards
  (oid: x509_RDN_attribute_oid)
  (t: directory_string_type)
  (lb: asn1_int32)
  (ub: asn1_value_int32_of_type t { lb <= ub })
: Tot (serializer32_backwards (serialize_RDN oid t lb ub))

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

noextract inline_for_extraction
let get_RDN_x520_attribute_string
  (#t: x520_attribute_t)
  (#string_t: directory_string_type { ((t == COUNTRY) ==> (string_t == PRINTABLE_STRING)) })
  (x: x509_RDN_x520_attribute_t t string_t)
: Tot (x509_RDN_x520_attribute_string_t t string_t)
=
  (* FIXME: This one no longer work after I moved it to interface. *)
  // snd (coerce_envelop
  //       (SET)
  //       (SEQUENCE)
  //       ((x520_attribute_oid t) `serialize_envelop_OID_with`
  //         serialize_asn1_character_string_with_character_bound string_t (x520_attribute_lb t) (x520_attribute_ub t))
  //       (x))
  [@inline_let] let f
    (#t: x520_attribute_t)
    (#string_t: directory_string_type { ((t == COUNTRY) ==> (string_t == PRINTABLE_STRING)) })
    (x: x509_RDN_t
          (x520_attribute_oid t)
          (string_t)
          (x520_attribute_lb t)
          (x520_attribute_ub t))
    : (x520_attribute_oid t) `envelop_OID_with_t`
      (asn1_string_with_character_bound_t
        (string_t)
        (count_character string_t)
        (x520_attribute_lb t)
        (x520_attribute_ub t))
  = x in
  snd (f x)

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


(*)
val lemma_serialize_RDN_unfold
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

(* Attribute *)

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

inline_for_extraction
let x520_attribute_oid
  (t: x520_attribute_t)
: Tot (datatype_of_asn1_type OID)
= match t with
  | COUNTRY      -> OID_AT_COUNTRY
  | ORGANIZATION -> OID_AT_ORGANIZATION
  | COMMON_NAME  -> OID_AT_CN

inline_for_extraction
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
= asn1_string_with_character_bound_t
    (string_t)
    (count_character string_t)
    (x520_attribute_lb t)
    (x520_attribute_ub t)

val parse_RDN_x520_attribute
  (t: x520_attribute_t)
  (string_t: directory_string_type { ((t == COUNTRY) ==> (string_t == PRINTABLE_STRING)) })
: parser (parse_asn1_envelop_tag_with_TLV_kind (SET)) (x509_RDN_x520_attribute_t t string_t)

val serialize_RDN_x520_attribute
  (t: x520_attribute_t)
  (string_t: directory_string_type { ((t == COUNTRY) ==> (string_t == PRINTABLE_STRING)) })
: serializer (parse_RDN_x520_attribute t string_t)

noextract inline_for_extraction
val serialize32_RDN_x520_attribute_backwards
  (t: x520_attribute_t)
  (string_t: directory_string_type { ((t == COUNTRY) ==> (string_t == PRINTABLE_STRING)) })
: serializer32_backwards (serialize_RDN_x520_attribute t string_t)

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

let f
  (#t: x520_attribute_t)
  (#string_t: directory_string_type { ((t == COUNTRY) ==> (string_t == PRINTABLE_STRING)) })
  (payload: x509_RDN_t
              (x520_attribute_oid t)
              (string_t)
              (x520_attribute_lb t)
              (x520_attribute_ub t))
: (x520_attribute_oid t) `envelop_OID_with_t`
  (asn1_string_with_character_bound_t
    (string_t)
    (count_character string_t)
    (x520_attribute_lb t)
    (x520_attribute_ub t))
= payload

noextract inline_for_extraction
let get_RDN_x520_attribute_string
  (#t: x520_attribute_t)
  (#string_t: directory_string_type { ((t == COUNTRY) ==> (string_t == PRINTABLE_STRING)) })
  (x: x509_RDN_x520_attribute_t t string_t)
: Tot (x509_RDN_x520_attribute_string_t t string_t)
=
  (* FIXME: This one no longer work after I moved it to interface. *)
  // snd (coerce_envelop
  //       (SET)
  //       (SEQUENCE)
  //       ((x520_attribute_oid t) `serialize_envelop_OID_with`
  //         serialize_asn1_character_string_with_character_bound string_t (x520_attribute_lb t) (x520_attribute_ub t))
  //       (x))
  [@inline_let] let f
    (#t: x520_attribute_t)
    (#string_t: directory_string_type { ((t == COUNTRY) ==> (string_t == PRINTABLE_STRING)) })
    (x: x509_RDN_t
          (x520_attribute_oid t)
          (string_t)
          (x520_attribute_lb t)
          (x520_attribute_ub t))
    : (x520_attribute_oid t) `envelop_OID_with_t`
      (asn1_string_with_character_bound_t
        (string_t)
        (count_character string_t)
        (x520_attribute_lb t)
        (x520_attribute_ub t))
  = x in
  snd (f x)

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
