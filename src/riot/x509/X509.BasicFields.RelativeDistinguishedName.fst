module X509.BasicFields.RelativeDistinguishedName

open LowParse.Low.Base

open ASN1.Spec
open ASN1.Low

open X509.Base

open FStar.Integers

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

let directory_string_value
  (t: directory_string_type)
= datatype_of_asn1_type t

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

let serialize_directory_string_with_character_bound_of_type
  (t: directory_string_type)
= match t with
  | IA5_STRING -> serialize_asn1_ia5_string_TLV_with_character_bound

let x509_RDN_t
  (oid: x509_RDN_attribute_oid)
  (lb: asn1_int32)
  (ub: asn1_int32 { lb <= ub })
  (t: directory_string_type)
= SET `inbound_envelop_tag_with_value_of`
  (**) (SEQUENCE `serialize_asn1_envelop_tag_with_TLV`
       (**) (oid `serialize_envelop_OID_with`
       (**)  serialize_directory_string_with_character_bound_of_type t lb ub))

let parse_RDN
  (oid: x509_RDN_attribute_oid)
  (lb: asn1_int32)
  (ub: asn1_int32 { lb <= ub })
  (t: directory_string_type)
: parser (parse_asn1_envelop_tag_with_TLV_kind (SET)) (x509_RDN_t oid lb ub t)
= (x509_RDN_t oid lb ub t)
  `coerce_parser`
  (SET `parse_asn1_envelop_tag_with_TLV`
  (**) (SEQUENCE `serialize_asn1_envelop_tag_with_TLV`
       (**) (oid `serialize_envelop_OID_with`
       (**)  serialize_directory_string_with_character_bound_of_type t lb ub)))

let serialize_RDN
  (oid: x509_RDN_attribute_oid)
  (lb: asn1_int32)
  (ub: asn1_int32 { lb <= ub })
  (t: directory_string_type)
: serializer (parse_RDN oid lb ub t)
= coerce_parser_serializer
    (parse_RDN oid lb ub t)
    (SET `serialize_asn1_envelop_tag_with_TLV`
    (**) (SEQUENCE `serialize_asn1_envelop_tag_with_TLV`
         (**) (oid `serialize_envelop_OID_with`
         (**)  serialize_directory_string_with_character_bound_of_type t lb ub)))
    ()

let lemma_serialize_RDN_unfold
  (oid: x509_RDN_attribute_oid)
  (lb: asn1_int32)
  (ub: asn1_int32 { lb <= ub })
  (t: directory_string_type)
  (x: x509_RDN_t oid lb ub t)
: Lemma ( predicate_serialize_asn1_envelop_tag_with_TLV_unfold
            (SET)
            (**) (SEQUENCE `serialize_asn1_envelop_tag_with_TLV`
                 (**) (oid `serialize_envelop_OID_with`
                 (**)  serialize_directory_string_with_character_bound_of_type t lb ub))
            (x) )
= lemma_serialize_asn1_envelop_tag_with_TLV_unfold
    (SET)
    (**) (SEQUENCE `serialize_asn1_envelop_tag_with_TLV`
         (**) (oid `serialize_envelop_OID_with`
         (**)  serialize_directory_string_with_character_bound_of_type t lb ub))
    (x)

let lemma_serialize_RDN_size
  (oid: x509_RDN_attribute_oid)
  (lb: asn1_int32)
  (ub: asn1_int32 { lb <= ub })
  (t: directory_string_type)
  (x: x509_RDN_t oid lb ub t)
: Lemma ( predicate_serialize_asn1_envelop_tag_with_TLV_size
            (SET)
            (**) (SEQUENCE `serialize_asn1_envelop_tag_with_TLV`
                 (**) (oid `serialize_envelop_OID_with`
                 (**)  serialize_directory_string_with_character_bound_of_type t lb ub))
            (x) )
= lemma_serialize_asn1_envelop_tag_with_TLV_size
    (SET)
    (**) (SEQUENCE `serialize_asn1_envelop_tag_with_TLV`
         (**) (oid `serialize_envelop_OID_with`
         (**)  serialize_directory_string_with_character_bound_of_type t lb ub))
    (x)


// let x509_RDN_ub_CommonName: asn1_int32 = 32768ul
// let parse_x509_CommonName = parse_RDN OID_AT_CN 0ul x509_RDN_ub_CommonName

// let x509_RDN_ub_Country: asn1_int32 = 32768ul
// let parse_x509_Country = parse_RDN OID_AT_COUNTRY 0ul x509_RDN_ub_Country

// let x509_RDN_ub_Organization: asn1_int32 = 64ul
// let parse_x509_Organization = parse_RDN OID_AT_ORGANIZATION 0ul x509_RDN_ub_Organization


type x501_name_t =
| COUNTRY
| ORGANIZATION
// | ORGANIZATIONAL_UNIT
// | DISTINGUISHED_NAME_QUALIFIER
// | STATE_OR_PROVINCE_NAME
| COMMON_NAME
// | SERIAL_NUMBER

#push-options "--ifuel 1"
let x501_name_lb
  (t: x501_name_t)
: Tot (asn1_int32)
= match t with
  | COUNTRY
  | ORGANIZATION
  | COMMON_NAME -> 0ul

let x501_name_ub
  (t: x501_name_t)
: Tot (len: asn1_int32 { len >= x501_name_lb t })
= match t with
  | COUNTRY      -> 2ul
  | ORGANIZATION -> 64ul
  | COMMON_NAME  -> 32768ul

let x501_name_oid
  (t: x501_name_t)
: Tot (datatype_of_asn1_type OID)
= match t with
  | COUNTRY      -> OID_AT_COUNTRY
  | ORGANIZATION -> OID_AT_ORGANIZATION
  | COMMON_NAME  -> OID_AT_CN

let x509_RDN_name_t
  (t: x501_name_t)
  (string_t: directory_string_type { ((t == COUNTRY) ==> (string_t == PRINTABLE_STRING)) })
= x509_RDN_t (x501_name_oid t) (x501_name_lb t) (x501_name_ub t) string_t

let parse_RDN_name
  (t: x501_name_t)
  (string_t: directory_string_type { ((t == COUNTRY) ==> (string_t == PRINTABLE_STRING)) })
: parser (parse_asn1_envelop_tag_with_TLV_kind (SET)) (x509_RDN_name_t t string_t)
= (x509_RDN_name_t t string_t)
  `coerce_parser`
  (parse_RDN (x501_name_oid t) (x501_name_lb t) (x501_name_ub t) string_t)

let serialize_RDN_name
  (t: x501_name_t)
  (string_t: directory_string_type { ((t == COUNTRY) ==> (string_t == PRINTABLE_STRING)) })
: serializer (parse_RDN_name t string_t)
= coerce_parser_serializer
    (parse_RDN_name t string_t)
    (serialize_RDN (x501_name_oid t) (x501_name_lb t) (x501_name_ub t) string_t)
    ()

let lemma_serialize_RDN_name_unfold
  (t: x501_name_t)
  (string_t: directory_string_type { ((t == COUNTRY) ==> (string_t == PRINTABLE_STRING)) })
= lemma_serialize_RDN_unfold (x501_name_oid t) (x501_name_lb t) (x501_name_ub t) string_t

let lemma_serialize_RDN_name_size
  (t: x501_name_t)
  (string_t: directory_string_type { ((t == COUNTRY) ==> (string_t == PRINTABLE_STRING)) })
= lemma_serialize_RDN_size (x501_name_oid t) (x501_name_lb t) (x501_name_ub t) string_t

type issuer_payload_t = {
  issuer_CN     : x509_RDN_name_t COMMON_NAME  IA5_STRING;
  issuer_OrgName: x509_RDN_name_t ORGANIZATION IA5_STRING;
  issuer_Country: x509_RDN_name_t COUNTRY      PRINTABLE_STRING
}

let parse_issuer_payload
= parse_RDN_name COMMON_NAME IA5_STRING
  `nondep_then`
  parse_RDN_name ORGANIZATION IA5_STRING
  `nondep_then`
  parse_RDN_name COUNTRY PRINTABLE_STRING

(* 1. option; 2. choice; 3. default; 4. list *)

(*)
let serialize32_RDN_backwards
  (oid: x509_RDN_attribute_oid)
  (t: directory_string_type)
  (lb: asn1_int32)
  (ub: asn1_int32 { lb <= ub })
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

