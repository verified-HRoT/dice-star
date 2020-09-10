module X509.ExtFields.AuthorityKeyIdentifier

open LowParse.Spec.Base
open LowParse.Spec.Combinators

open ASN1.Base
open ASN1.Spec

open X509.Base

module B32 = FStar.Bytes

open FStar.Integers

open ASN1.Low

open X509.BasicFields.RelativeDistinguishedName
open X509.BasicFields.SerialNumber

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

(* Example `DEFAULT` *)
let pd =
  parse_asn1_TLV_of_type INTEGER
  `parse_synth`
  (fun x -> match x with 0l -> None | _ -> Some x)

(* Example `OPTIONAL` *)
(* NOTE: This might be CSG, you need to look at explicit tag *)
(* NOTE: Statically determine this. *)

let x509_keyIdentifier_t
= (CUSTOM_TAG CONTEXT_SPECIFIC CONSTRUCTED 0uy) `inbound_envelop_tag_with_value_of`
  (**) (serialize_asn1_TLV_of_type OCTET_STRING)

// let x509_generalNames_t
// = (CUSTOM_TAG CONTEXT_SPECIFIC CONSTRUCTED 0uy) `inbound_envelop_tag_with_value_of`
//   (**) (serialize_)

let x509_authorityCertSerialNumber_t
= (CUSTOM_TAG CONTEXT_SPECIFIC CONSTRUCTED 2uy) `inbound_envelop_tag_with_value_of`
  (**) (serialize_x509_serialNumber)

// let f
//   (t_last: Type)
//   (b: bool)
//   (t: Type)
//   (g: Type -> bool -> Type -> Type)
// : Type -> bool -> Type -> Type
// = if t_last = unit then
//   else
//     fun t' b t'' -> t_last `tuple2` (g (if b then t else unit) b t'')

noextract inline_for_extraction
let x509_authKeyID_t
  (has_keyID: bool)
  (has_authCertSN: bool)
: Type
= unit
