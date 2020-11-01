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

let serialize32_x509_authKeyID_keyIdentifier_backwards
= serialize32_asn1_octet_string_TLV_with_tag_backwards x509_authKeyID_keyIdentifier_tag

let lemma_serialize_x509_authKeyID_keyIdentifier_size_exact x
= lemma_serialize_x509_authKeyID_keyIdentifier_size x
