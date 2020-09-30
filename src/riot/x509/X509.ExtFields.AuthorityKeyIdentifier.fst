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

(* Not supporting them for now *)
// let x509_authKeyID_CertIssuer_tag: asn1_tag_t
// = (CUSTOM_TAG CONTEXT_SPECIFIC CONSTRUCTED 1uy)

// let x509_authKeyID_CertSN_tag: asn1_tag_t
// = (CUSTOM_TAG CONTEXT_SPECIFIC CONSTRUCTED 2uy)

(* keyIdentifier *)

let parse_x509_authKeyID_keyIdentifier
= x509_authKeyID_keyIdentifier_tag `parse_asn1_envelop_tag_with_TLV`
  (**) (serialize_asn1_TLV_of_type OCTET_STRING)

let serialize_x509_authKeyID_keyIdentifier
= x509_authKeyID_keyIdentifier_tag `serialize_asn1_envelop_tag_with_TLV`
  (**) (serialize_asn1_TLV_of_type OCTET_STRING)

let serialize32_x509_authKeyID_keyIdentifier_backwards
= x509_authKeyID_keyIdentifier_tag `serialize32_asn1_envelop_tag_with_TLV_backwards`
  (**) (serialize32_asn1_TLV_backwards_of_type OCTET_STRING)

let lemma_serialize_x509_authKeyID_keyIdentifier_unfold x
= lemma_serialize_asn1_envelop_tag_with_TLV_unfold
    (x509_authKeyID_keyIdentifier_tag)
    (serialize_asn1_TLV_of_type OCTET_STRING)
    (x)

let lemma_serialize_x509_authKeyID_keyIdentifier_size x
= lemma_serialize_asn1_envelop_tag_with_TLV_size
    (x509_authKeyID_keyIdentifier_tag)
    (serialize_asn1_TLV_of_type OCTET_STRING)
    (x)

let lemma_serialize_x509_authKeyID_keyIdentifier_size_exact x
= lemma_serialize_x509_authKeyID_keyIdentifier_size x

// let has_x509_keyIdentifier_t b
// = if b then Some x509_keyIdentifier_t else None

// let x509_generalNames_t
// = (CUSTOM_TAG CONTEXT_SPECIFIC CONSTRUCTED 0uy) `inbound_envelop_tag_with_value_of`
//   (**) (serialize_)

// let x509_authorityCertSerialNumber_t
// = (CUSTOM_TAG CONTEXT_SPECIFIC CONSTRUCTED 2uy) `inbound_envelop_tag_with_value_of`
//   (**) (serialize_x509_serialNumber)


// noextract inline_for_extraction
// let x509_authKeyID_t
//   (has_keyID: bool)
//   (has_authCertSN: bool)
// // : Type
// = (has_x509_keyIdentifier_t
//    `combine`
//    has_x509_keyIdentifier_t)
//   (has_keyID, has_authCertSN)


// (* Example `DEFAULT` *)
// let pd =
//   parse_asn1_TLV_of_type INTEGER
//   `parse_synth`
//   (fun x -> match x with 0l -> None | _ -> Some x)

// (* Example `OPTIONAL` *)
// (* NOTE: This might be CSG, you need to look at explicit tag *)
// (* NOTE: Statically determine this. *)

// #push-options "--fuel 0 --ifuel 0"
// let combine
//   (#t1: Type)
//   (f: t1 -> option Type)
//   (#t2: Type)
//   (g: t2 -> option Type)
// : (t1 `tuple2` t2) -> option Type
// = fun (a, b) ->
//   match f a, g b with
//   | Some x, Some y -> Some (x `tuple2` y)
//   | Some x, None   -> Some x
//   | None  , Some y -> Some y
//   | None  , None   -> None
