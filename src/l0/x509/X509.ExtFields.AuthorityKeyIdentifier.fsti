module X509.ExtFields.AuthorityKeyIdentifier

open LowParse.Spec.Base
open LowParse.Spec.Combinators

open ASN1.Base
open ASN1.Spec
open ASN1.Low


open X509.Base

module B32 = FStar.Bytes

open FStar.Integers

// open X509.BasicFields.RelativeDistinguishedName
// open X509.BasicFields.SerialNumber

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
= (CUSTOM_TAG CONTEXT_SPECIFIC PRIMITIVE 0uy)

(* Not supporting them for now *)
// let x509_authKeyID_CertIssuer_tag: asn1_tag_t
// = (CUSTOM_TAG CONTEXT_SPECIFIC CONSTRUCTED 1uy)

// let x509_authKeyID_CertSN_tag: asn1_tag_t
// = (CUSTOM_TAG CONTEXT_SPECIFIC CONSTRUCTED 2uy)

(* keyIdentifier *)

let x509_authKeyID_keyIdentifier_t
= datatype_of_asn1_type OCTET_STRING

let parse_x509_authKeyID_keyIdentifier
: parser _ x509_authKeyID_keyIdentifier_t
= parse_asn1_octet_string_TLV_with_tag x509_authKeyID_keyIdentifier_tag

let serialize_x509_authKeyID_keyIdentifier
: serializer parse_x509_authKeyID_keyIdentifier
= serialize_asn1_octet_string_TLV_with_tag x509_authKeyID_keyIdentifier_tag

noextract inline_for_extraction
val serialize32_x509_authKeyID_keyIdentifier_backwards
: serializer32_backwards serialize_x509_authKeyID_keyIdentifier

unfold
let lemma_serialize_x509_authKeyID_keyIdentifier_unfold
= lemma_serialize_asn1_octet_string_TLV_with_tag_unfold x509_authKeyID_keyIdentifier_tag

unfold
let lemma_serialize_x509_authKeyID_keyIdentifier_size
= lemma_serialize_asn1_octet_string_TLV_with_tag_size x509_authKeyID_keyIdentifier_tag

let length_of_x509_authKeyID_keyIdentifier
  (keyID: datatype_of_asn1_type OCTET_STRING)
: GTot (asn1_TLV_length_of_type OCTET_STRING)
= length_of_asn1_primitive_TLV #OCTET_STRING keyID

let len_of_x509_authKeyID_keyIdentifier
  (keyID: datatype_of_asn1_type OCTET_STRING)
: Tot (len: asn1_TLV_int32_of_type OCTET_STRING
            { v len == length_of_x509_authKeyID_keyIdentifier keyID })
= len_of_asn1_primitive_TLV #OCTET_STRING keyID

val lemma_serialize_x509_authKeyID_keyIdentifier_size_exact
  (x: x509_authKeyID_keyIdentifier_t)
: Lemma (
  length_of_opaque_serialization serialize_x509_authKeyID_keyIdentifier x ==
  length_of_x509_authKeyID_keyIdentifier x
)

let x509_get_authKeyID_keyIdentifier
  (keyID: datatype_of_asn1_type OCTET_STRING)
: Tot (x509_authKeyID_keyIdentifier_t)
= keyID
