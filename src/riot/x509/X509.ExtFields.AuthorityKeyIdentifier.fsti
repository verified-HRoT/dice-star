module X509.ExtFields.AuthorityKeyIdentifier

open LowParse.Spec.Base
open LowParse.Spec.Combinators

open ASN1.Base
open ASN1.Spec
open ASN1.Low


open X509.Base

module B32 = FStar.Bytes

open FStar.Integers

open X509.BasicFields.RelativeDistinguishedName
open X509.BasicFields.SerialNumber

#set-options "--z3rlimit 64 --fuel 0 --ifuel 0"

(* 4.2.1.1.  Authority Key Identifier

   ...

   The value of the keyIdentifier field SHOULD be derived from the
   public key used to verify the certificate's signature or a method
   that generates unique values.  Two common methods for generating key
   identifiers from the public key are described in Section 4.2.1.2.
   Where a key identifier has not been previously established, this
   specification RECOMMENDS use of one of these methods for generating
   keyIdentifiers or use of a similar method that uses a different hash
   algorithm.  Where a key identifier has been previously established,
   the CA SHOULD use the previously established identifier.

   This profile RECOMMENDS support for the key identifier method by all
   certificate users.

   Conforming CAs MUST mark this extension as non-critical.

   id-ce-authorityKeyIdentifier OBJECT IDENTIFIER ::=  { id-ce 35 }

   AuthorityKeyIdentifier ::= SEQUENCE {
      keyIdentifier             [0] KeyIdentifier           OPTIONAL,
      authorityCertIssuer       [1] GeneralNames            OPTIONAL,
      authorityCertSerialNumber [2] CertificateSerialNumber OPTIONAL  }

   KeyIdentifier ::= OCTET STRING

 *)

let x509_authKeyID_keyIdentifier_tag: asn1_tag_t
= (CUSTOM_TAG CONTEXT_SPECIFIC CONSTRUCTED 0uy)

(* Not supporting them for now *)
// let x509_authKeyID_CertIssuer_tag: asn1_tag_t
// = (CUSTOM_TAG CONTEXT_SPECIFIC CONSTRUCTED 1uy)

// let x509_authKeyID_CertSN_tag: asn1_tag_t
// = (CUSTOM_TAG CONTEXT_SPECIFIC CONSTRUCTED 2uy)

(* keyIdentifier *)

let x509_authKeyID_keyIdentifier_t
= x509_authKeyID_keyIdentifier_tag `inbound_envelop_tag_with_value_of`
  (**) (serialize_asn1_TLV_of_type OCTET_STRING)

let parse_x509_authKeyID_keyIdentifier
: parser _ x509_authKeyID_keyIdentifier_t
= x509_authKeyID_keyIdentifier_tag `parse_asn1_envelop_tag_with_TLV`
  (**) (serialize_asn1_TLV_of_type OCTET_STRING)

let serialize_x509_authKeyID_keyIdentifier
: serializer parse_x509_authKeyID_keyIdentifier
= x509_authKeyID_keyIdentifier_tag `serialize_asn1_envelop_tag_with_TLV`
  (**) (serialize_asn1_TLV_of_type OCTET_STRING)

val serialize32_x509_authKeyID_keyIdentifier_backwards
: serializer32_backwards serialize_x509_authKeyID_keyIdentifier

val lemma_serialize_x509_authKeyID_keyIdentifier_unfold
  (x: x509_authKeyID_keyIdentifier_t)
: Lemma (
  predicate_serialize_asn1_envelop_tag_with_TLV_unfold
    (x509_authKeyID_keyIdentifier_tag)
    (serialize_asn1_TLV_of_type OCTET_STRING)
    (x)
)

val lemma_serialize_x509_authKeyID_keyIdentifier_size
  (x: x509_authKeyID_keyIdentifier_t)
: Lemma (
  predicate_serialize_asn1_envelop_tag_with_TLV_size
    (x509_authKeyID_keyIdentifier_tag)
    (serialize_asn1_TLV_of_type OCTET_STRING)
    (x)
)

let valid_authKeyID_keyIdentifier_ingredients
  (keyID: datatype_of_asn1_type OCTET_STRING)
: Type0
= length_of_asn1_primitive_TLV keyID
  <= asn1_value_length_max_of_type x509_authKeyID_keyIdentifier_tag

let length_of_x509_authKeyID_keyIdentifier
  (keyID: datatype_of_asn1_type OCTET_STRING
          { valid_authKeyID_keyIdentifier_ingredients keyID })
: GTot (asn1_TLV_length_of_type x509_authKeyID_keyIdentifier_tag)
= length_of_TLV
    (x509_authKeyID_keyIdentifier_tag)
    (length_of_asn1_primitive_TLV keyID)

let len_of_x509_authKeyID_keyIdentifier
  (keyID: datatype_of_asn1_type OCTET_STRING
          { valid_authKeyID_keyIdentifier_ingredients keyID })
: Tot (len: asn1_TLV_int32_of_type x509_authKeyID_keyIdentifier_tag
            { v len == length_of_x509_authKeyID_keyIdentifier keyID })
= len_of_TLV
    (x509_authKeyID_keyIdentifier_tag)
    (len_of_asn1_primitive_TLV keyID)

val lemma_serialize_x509_authKeyID_keyIdentifier_size_exact
  (x: x509_authKeyID_keyIdentifier_t)
: Lemma (
  length_of_opaque_serialization serialize_x509_authKeyID_keyIdentifier x ==
  length_of_x509_authKeyID_keyIdentifier x
)

let x509_get_authKeyID_keyIdentifier
  (keyID: datatype_of_asn1_type OCTET_STRING
          { valid_authKeyID_keyIdentifier_ingredients keyID })
: Tot (x509_authKeyID_keyIdentifier_t)
= keyID
