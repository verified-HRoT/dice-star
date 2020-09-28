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

let serialize32_RDN_payload_backwards oid t lb ub
= (oid `serialize32_envelop_OID_with_backwards`
   serialize32_asn1_character_string_with_character_bound_backwards t lb ub)

let parse_RDN oid t lb ub
= (x509_RDN_t oid t lb ub)
  `coerce_parser`
  (SET `parse_asn1_envelop_tag_with_TLV`
  (**) (SEQUENCE `serialize_asn1_envelop_tag_with_TLV`
       (**) (serialize_RDN_payload oid t lb ub)))

let serialize_RDN oid t lb ub
= coerce_parser_serializer
    (parse_RDN oid t lb ub)
    (SET `serialize_asn1_envelop_tag_with_TLV`
    (**) (SEQUENCE `serialize_asn1_envelop_tag_with_TLV`
       (**) (serialize_RDN_payload oid t lb ub)))
    ()

let lemma_serialize_RDN_unfold oid t lb ub x
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

let lemma_serialize_RDN_size oid t lb ub x
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

let lemma_serialize_RDN_size_exact oid t lb ub x
= lemma_serialize_RDN_unfold oid t lb ub x;
  lemma_serialize_RDN_size   oid t lb ub x;
  lemma_serialize_envelop_OID_with_size
    (oid)
    (serialize_asn1_character_string_with_character_bound t lb ub)
    (x);
  // lemma_serialize_asn1_oid_TLV_of_size oid oid
()

#push-options "--ifuel 1"

let serialize32_RDN_backwards oid t lb ub
= coerce_serializer32_backwards
  (* s2  *) (serialize_RDN oid t lb ub)
  (* s32 *) (SET `serialize32_asn1_envelop_tag_with_TLV_backwards`
            (**) (SEQUENCE `serialize32_asn1_envelop_tag_with_TLV_backwards`
                 (**) (serialize32_RDN_payload_backwards oid t lb ub)))
  (* prf *) ()

(*  *)

let lemma_RDN_x520_attribute_size #t #string_t s
= lemma_serialize_character_string_size string_t s;
  lemma_serialize_asn1_oid_TLV_of_size (x520_attribute_oid t) (x520_attribute_oid t);
  lemma_serialize_envelop_OID_with_size
    (x520_attribute_oid t)
    (serialize_asn1_TLV_of_type string_t)
    ((x520_attribute_oid t), s)

let parse_RDN_x520_attribute t string_t
= (x509_RDN_x520_attribute_t t string_t)
  `coerce_parser`
  (parse_RDN (x520_attribute_oid t) (string_t) (x520_attribute_lb t) (x520_attribute_ub t))

let serialize_RDN_x520_attribute t string_t
= coerce_parser_serializer
    (parse_RDN_x520_attribute t string_t)
    (serialize_RDN (x520_attribute_oid t) (string_t) (x520_attribute_lb t) (x520_attribute_ub t))
    ()


#push-options "--z3rlimit 64"
let lemma_serialize_RDN_x520_attribute_size_exact #t #string_t x
= lemma_serialize_RDN_size_exact (x520_attribute_oid t) (string_t) (x520_attribute_lb t) (x520_attribute_ub t) x
#pop-options

#push-options "--z3rlimit 96"
let serialize32_RDN_x520_attribute_backwards t string_t
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

