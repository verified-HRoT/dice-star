module X509.ExtFields.BasicConstraints

open ASN1.Spec
open ASN1.Low

open X509.Base
open X509.BasicFields.Extension2

open FStar.Integers

#set-options "--z3rlimit 64 --fuel 0 --ifuel 0"

(* RFC 5280  4.2.1.9.  Basic Constraints
   The basic constraints extension identifies whether the subject of the
   certificate is a CA and the maximum depth of valid certification
   paths that include this certificate.

   The cA boolean indicates whether the certified public key may be used
   to verify certificate signatures.  If the cA boolean is not asserted,
   then the keyCertSign bit in the key usage extension MUST NOT be
   asserted.  If the basic constraints extension is not present in a
   version 3 certificate, or the extension is present but the cA boolean
   is not asserted, then the certified public key MUST NOT be used to
   verify certificate signatures.

   The pathLenConstraint field is meaningful only if the cA boolean is
   asserted and the key usage extension, if present, asserts the
   keyCertSign bit (Section 4.2.1.3).  In this case, it gives the
   maximum number of non-self-issued intermediate certificates that may
   follow this certificate in a valid certification path.  (Note: The
   last certificate in the certification path is not an intermediate
   certificate, and is not included in this limit.  Usually, the last
   certificate is an end entity certificate, but it can be a CA
   certificate.)  A pathLenConstraint of zero indicates that no non-
   self-issued intermediate CA certificates may follow in a valid
   certification path.  Where it appears, the pathLenConstraint field
   MUST be greater than or equal to zero.  Where pathLenConstraint does
   not appear, no limit is imposed.

   Conforming CAs MUST include this extension in all CA certificates
   that contain public keys used to validate digital signatures on
   certificates and MUST mark the extension as critical in such
   certificates.  This extension MAY appear as a critical or non-
   critical extension in CA certificates that contain public keys used
   exclusively for purposes other than validating digital signatures on
   certificates.  Such CA certificates include ones that contain public
   keys used exclusively for validating digital signatures on CRLs and
   ones that contain key management public keys used with certificate
   enrollment protocols.  This extension MAY appear as a critical or
   non-critical extension in end entity certificates.

   CAs MUST NOT include the pathLenConstraint field unless the cA
   boolean is asserted and the key usage extension asserts the
   keyCertSign bit.

   id-ce-basicConstraints OBJECT IDENTIFIER ::=  { id-ce 19 }

   BasicConstraints ::= SEQUENCE {
        cA                      BOOLEAN DEFAULT FALSE,
        pathLenConstraint       INTEGER (0..MAX) OPTIONAL }
 *)

let parse_x509_basicConstraints_extValue_payload isCA
= if isCA then
  ( parse_asn1_boolean_TLV_true
    `nondep_then`
    parse_asn1_TLV_of_type INTEGER )
  else
  ( parse_asn1_boolean_TLV_false )

let serialize_x509_basicConstraints_extValue_payload isCA
= if isCA then
  ( serialize_asn1_boolean_TLV_true
    `serialize_nondep_then`
    serialize_asn1_TLV_of_type INTEGER )
  else
  ( serialize_asn1_boolean_TLV_false )

let serialize32_x509_basicConstraints_extValue_payload_backwards isCA
= if isCA then
  ( serialize32_asn1_boolean_TLV_true_backwards ()
    `serialize32_nondep_then_backwards`
    serialize32_asn1_TLV_backwards_of_type INTEGER )
  else
  ( serialize32_asn1_boolean_TLV_false_backwards () )

let lemma_serialize_x509_basicConstraints_extValue_payload_unfold isCA x
= if isCA then
  ( serialize_nondep_then_eq
    (* s1 *) (serialize_asn1_boolean_TLV_true)
    (* s2 *) (serialize_asn1_TLV_of_type INTEGER)
    (* in *) x )
  else
  ( () )

// let valid_x509_basicConstraints_extValue_payload
//   (isCA: bool)
// : ( if isCA then
//     ( datatype_of_asn1_type INTEGER -> Type0 )
//     else
//     ( Type0 ) )
// = if isCA then
//   ( fun (pathLen: datatype_of_asn1_type INTEGER) ->
//     length_of_x509_basicConstraints_extValue_payload true pathLen
//     <= asn1_value_length_max_of_type OCTET_STRING )
//   <: datatype_of_asn1_type INTEGER -> Type0
//   else
//   ( True )

let lemma_serialize_x509_basicConstraints_extValue_payload_size isCA x
= lemma_serialize_x509_basicConstraints_extValue_payload_unfold isCA x

(* extValue *)

let parse_x509_basicConstraints_extValue isCA
= x509_basicConstraints_extValue_t isCA
  `coerce_parser`
  parse_asn1_sequence_TLV
  (**) (serialize_x509_basicConstraints_extValue_payload isCA)

let serialize_x509_basicConstraints_extValue isCA
= coerce_parser_serializer
    (parse_x509_basicConstraints_extValue isCA)
    (serialize_asn1_sequence_TLV
    (**) (serialize_x509_basicConstraints_extValue_payload isCA))
    ()

let serialize32_x509_basicConstraints_extValue_backwards isCA
= coerce_serializer32_backwards
    (serialize_x509_basicConstraints_extValue isCA)
    (serialize32_asn1_sequence_TLV_backwards
    (**) (serialize32_x509_basicConstraints_extValue_payload_backwards isCA))
    ()

let lemma_serialize_x509_basicConstraints_extValue_unfold isCA x
= lemma_serialize_asn1_sequence_TLV_unfold
    (serialize_x509_basicConstraints_extValue_payload isCA)
    (x)

let lemma_serialize_x509_basicConstraints_extValue_size isCA x
= lemma_serialize_asn1_sequence_TLV_size
    (serialize_x509_basicConstraints_extValue_payload isCA)
    (x)

let lemma_serialize_x509_basicConstraints_extValue_size_exact isCA x
= lemma_serialize_x509_basicConstraints_extValue_unfold isCA x;
  lemma_serialize_x509_basicConstraints_extValue_size isCA x;
    lemma_serialize_x509_basicConstraints_extValue_payload_size isCA x

(* ext *)

let parse_x509_basicConstraints isCA
= x509_basicConstraints_t isCA
  `coerce_parser`
  parse_x509_extension
  (**) (OID_BASIC_CONSTRAINTS)
  (**) (serialize_x509_basicConstraints_extValue isCA)

let serialize_x509_basicConstraints isCA
= coerce_parser_serializer
    (parse_x509_basicConstraints isCA)
    (serialize_x509_extension
    (**) (OID_BASIC_CONSTRAINTS)
    (**) (serialize_x509_basicConstraints_extValue isCA))
    ()

let serialize32_x509_basicConstraints_backwards isCA
= coerce_serializer32_backwards
    (_)
    (serialize32_x509_extension_backwards
    (**) (OID_BASIC_CONSTRAINTS)
    (**) (serialize32_x509_basicConstraints_extValue_backwards isCA))
    ()

let lemma_serialize_x509_basicConstraints_unfold isCA x
= lemma_serialize_x509_extension_unfold
  (**) (OID_BASIC_CONSTRAINTS)
  (**) (serialize_x509_basicConstraints_extValue isCA)
  (**) (x)

let lemma_serialize_x509_basicConstraints_size isCA x
= lemma_serialize_x509_extension_size
  (**) (OID_BASIC_CONSTRAINTS)
  (**) (serialize_x509_basicConstraints_extValue isCA)
  (**) (x)

let lemma_serialize_x509_basicConstraints_size_exact isCA ext
= if isCA then
  ( lemma_serialize_x509_basicConstraints_extValue_size_exact isCA (snd ext);
    lemma_serialize_x509_basicConstraints_extValue_payload_size isCA (snd ext);
    lemma_serialize_x509_extension_size_exact
      (OID_BASIC_CONSTRAINTS)
      (serialize_x509_basicConstraints_extValue isCA)
      (ext)
      (v (len_of_x509_basicConstraints_extValue true (snd (snd ext <: x509_basicConstraints_extValue_payload_t true))) ))
  else
  ( lemma_serialize_x509_basicConstraints_extValue_size_exact isCA (snd ext);
    lemma_serialize_x509_basicConstraints_extValue_payload_size isCA (snd ext);
    lemma_serialize_x509_extension_size_exact
      (OID_BASIC_CONSTRAINTS)
      (serialize_x509_basicConstraints_extValue isCA)
      (ext)
      (v (len_of_x509_basicConstraints_extValue false) ))

(* FIXME: Does not type check for some reason *)
(*
let x509_get_basicConstraints
  (isCA: bool)
  (criticality: datatype_of_asn1_type BOOLEAN)
: Tot (
  if isCA then
  ( datatype_of_asn1_type INTEGER -> Tot (x509_basicConstraints_t isCA) )
  else
  ( x509_basicConstraints_t isCA )
)
= if isCA then
  ( x509_get_basicConstraints_isCA isCA criticality )
  else
  ( x509_get_basicConstraints_isNotCA criticality )
