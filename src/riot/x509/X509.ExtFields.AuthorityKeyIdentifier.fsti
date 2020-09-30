module X509.ExtFields.AuthorityKeyIdentifier

open ASN1.Spec
open ASN1.Low

open X509.Base

open FStar.Integers

//open X509.BasicFields.RelativeDistinguishedName
//open X509.BasicFields.SerialNumber

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

noextract
val parse_x509_authKeyID_keyIdentifier
: parser (parse_asn1_envelop_tag_with_TLV_kind x509_authKeyID_keyIdentifier_tag) x509_authKeyID_keyIdentifier_t

noextract
val serialize_x509_authKeyID_keyIdentifier
: serializer parse_x509_authKeyID_keyIdentifier

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

let len_of_x509_authKeyID_keyIdentifier
  (keyID: datatype_of_asn1_type OCTET_STRING
          { valid_authKeyID_keyIdentifier_ingredients keyID })
: Tot (asn1_TLV_int32_of_type x509_authKeyID_keyIdentifier_tag)
= len_of_TLV
    (x509_authKeyID_keyIdentifier_tag)
    (len_of_asn1_primitive_TLV keyID)

val lemma_serialize_x509_authKeyID_keyIdentifier_size_exact
  (x: x509_authKeyID_keyIdentifier_t)
: Lemma (
  length_of_opaque_serialization serialize_x509_authKeyID_keyIdentifier x ==
  (v (len_of_x509_authKeyID_keyIdentifier x))
)

let x509_get_authKeyID_keyIdentifier
  (keyID: datatype_of_asn1_type OCTET_STRING
          { valid_authKeyID_keyIdentifier_ingredients keyID })
: Tot (x509_authKeyID_keyIdentifier_t)
= keyID

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
