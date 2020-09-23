module X509.ExtFields.BasicConstraints

open LowParse.Spec.Base
open LowParse.Spec.Combinators

open ASN1.Base
open ASN1.Spec
open ASN1.Low

open X509.Base
open X509.BasicFields.Extension2

module B32 = FStar.Bytes

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

noextract inline_for_extraction
let x509_basicConstraints_extValue_payload_t
  (isCA: bool)
= if isCA then
  ( asn1_boolean_true_t `tuple2` (datatype_of_asn1_type INTEGER) )
  else
  ( asn1_boolean_false_t )

let parse_x509_basicConstraints_extValue_payload_kind
  (isCA: bool)
: k: parser_kind {Mkparser_kind'?.parser_kind_subkind k == Some ParserStrong}
= if isCA then
  ( parse_asn1_TLV_kind_of_type BOOLEAN
    `and_then_kind`
    parse_asn1_TLV_kind_of_type INTEGER )
  else
  ( parse_asn1_TLV_kind_of_type BOOLEAN )

let parse_x509_basicConstraints_extValue_payload
  (isCA: bool)
: parser (parse_x509_basicConstraints_extValue_payload_kind isCA) (x509_basicConstraints_extValue_payload_t isCA)
= if isCA then
  ( parse_asn1_boolean_TLV_true
    `nondep_then`
    parse_asn1_TLV_of_type INTEGER )
  else
  ( parse_asn1_boolean_TLV_false )

let serialize_x509_basicConstraints_extValue_payload
  (isCA: bool)
: serializer (parse_x509_basicConstraints_extValue_payload isCA)
= if isCA then
  ( serialize_asn1_boolean_TLV_true
    `serialize_nondep_then`
    serialize_asn1_TLV_of_type INTEGER )
  else
  ( serialize_asn1_boolean_TLV_false )

noextract inline_for_extraction
let serialize32_x509_basicConstraints_extValue_payload_backwards
  (isCA: bool)
: serializer32_backwards (serialize_x509_basicConstraints_extValue_payload isCA)
= if isCA then
  ( serialize32_asn1_boolean_TLV_true_backwards ()
    `serialize32_nondep_then_backwards`
    serialize32_asn1_TLV_backwards_of_type INTEGER )
  else
  ( serialize32_asn1_boolean_TLV_false_backwards () )

let lemma_serialize_x509_basicConstraints_extValue_payload_unfold
  (isCA: bool)
  (x: x509_basicConstraints_extValue_payload_t isCA)
: Lemma (
  serialize (serialize_x509_basicConstraints_extValue_payload isCA) x ==
  ( if isCA then
    ( let x = x <: asn1_boolean_true_t `tuple2` datatype_of_asn1_type INTEGER in
      serialize (serialize_asn1_boolean_TLV_true) (fst x)
      `Seq.append`
      serialize (serialize_asn1_TLV_of_type INTEGER) (snd x) )
    else
    ( let x = x <: asn1_boolean_false_t in
      serialize (serialize_asn1_boolean_TLV_false) x ) )
)
= if isCA then
  ( serialize_nondep_then_eq
    (* s1 *) (serialize_asn1_boolean_TLV_true)
    (* s2 *) (serialize_asn1_TLV_of_type INTEGER)
    (* in *) x )
  else
  ( () )

let length_of_x509_basicConstraints_extValue_payload_hasLen
  (pathLen: datatype_of_asn1_type INTEGER)
: GTot (nat)
= length_of_asn1_primitive_TLV true +
  length_of_asn1_primitive_TLV pathLen

let length_of_x509_basicConstraints_extValue_payload
  (isCA: bool)
: GTot ( if isCA then
         ( datatype_of_asn1_type INTEGER -> GTot (asn1_value_length_of_type SEQUENCE) )
         else
         ( asn1_value_length_of_type SEQUENCE ) )
= if isCA then
  ( length_of_x509_basicConstraints_extValue_payload_hasLen )
  else
  ( length_of_asn1_primitive_TLV false )

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

let len_of_x509_basicConstraints_extValue_payload_hasLen
  (pathLen: datatype_of_asn1_type INTEGER)
            // { valid_x509_basicConstraints_extValue_payload true pathLen })
: Tot (len: asn1_value_int32_of_type SEQUENCE
            { v len == length_of_x509_basicConstraints_extValue_payload_hasLen pathLen })
= len_of_asn1_primitive_TLV true +
  len_of_asn1_primitive_TLV pathLen

noextract inline_for_extraction
let len_of_x509_basicConstraints_extValue_payload
  (isCA: bool)
: Tot ( if isCA then
         ( (pathLen: datatype_of_asn1_type INTEGER)
           -> Tot (len: asn1_value_int32_of_type SEQUENCE
                        { v len == length_of_x509_basicConstraints_extValue_payload true pathLen }) )
         else
         ( len: asn1_value_int32_of_type SEQUENCE
                { v len == length_of_x509_basicConstraints_extValue_payload false } ) )
= if isCA then
  ( len_of_x509_basicConstraints_extValue_payload_hasLen )
  else
  ( len_of_asn1_primitive_TLV false )

let lemma_serialize_x509_basicConstraints_extValue_payload_size
  (isCA: bool)
  (x: x509_basicConstraints_extValue_payload_t isCA)
: Lemma (
  Seq.length (serialize (serialize_x509_basicConstraints_extValue_payload isCA) x) ==
  ( if isCA then
    ( let x = x <: asn1_boolean_true_t `tuple2` datatype_of_asn1_type INTEGER in
      length_of_x509_basicConstraints_extValue_payload true (snd x)  )
    else
    ( length_of_x509_basicConstraints_extValue_payload false ) )
)
= lemma_serialize_x509_basicConstraints_extValue_payload_unfold isCA x

(* extValue *)

noextract inline_for_extraction
let x509_basicConstraints_extValue_t
  (isCA: bool)
: Type
= inbound_sequence_value_of
  (**) (serialize_x509_basicConstraints_extValue_payload isCA)

let parse_x509_basicConstraints_extValue
  (isCA: bool)
: parser _ (x509_basicConstraints_extValue_t isCA)
= x509_basicConstraints_extValue_t isCA
  `coerce_parser`
  parse_asn1_sequence_TLV
  (**) (serialize_x509_basicConstraints_extValue_payload isCA)

let serialize_x509_basicConstraints_extValue
  (isCA: bool)
: serializer (parse_x509_basicConstraints_extValue isCA)
= coerce_parser_serializer
    (parse_x509_basicConstraints_extValue isCA)
    (serialize_asn1_sequence_TLV
    (**) (serialize_x509_basicConstraints_extValue_payload isCA))
    ()

noextract inline_for_extraction
let serialize32_x509_basicConstraints_extValue_backwards
  (isCA: bool)
: serializer32_backwards (serialize_x509_basicConstraints_extValue isCA)
= coerce_serializer32_backwards
    (serialize_x509_basicConstraints_extValue isCA)
    (serialize32_asn1_sequence_TLV_backwards
    (**) (serialize32_x509_basicConstraints_extValue_payload_backwards isCA))
    ()

let lemma_serialize_x509_basicConstraints_extValue_unfold
  (isCA: bool)
  (x: x509_basicConstraints_extValue_t isCA)
: Lemma (
  predicate_serialize_asn1_sequence_TLV_unfold
    (serialize_x509_basicConstraints_extValue_payload isCA)
    (x)
)
= lemma_serialize_asn1_sequence_TLV_unfold
    (serialize_x509_basicConstraints_extValue_payload isCA)
    (x)

let lemma_serialize_x509_basicConstraints_extValue_size
  (isCA: bool)
  (x: x509_basicConstraints_extValue_t isCA)
: Lemma (
  predicate_serialize_asn1_sequence_TLV_size
    (serialize_x509_basicConstraints_extValue_payload isCA)
    (x)
)
= lemma_serialize_asn1_sequence_TLV_size
    (serialize_x509_basicConstraints_extValue_payload isCA)
    (x)

let length_of_x509_basicConstraints_extValue
  (isCA: bool)
: GTot ( if isCA then
         ( datatype_of_asn1_type INTEGER -> GTot (asn1_value_length_of_type OCTET_STRING) )
         else
         ( asn1_value_length_of_type OCTET_STRING ) )
= if isCA then
  ( fun (pathLen: datatype_of_asn1_type INTEGER) ->
      length_of_TLV
        (SEQUENCE)
        (length_of_x509_basicConstraints_extValue_payload true pathLen) )
  else
  ( length_of_TLV
      (SEQUENCE)
      (length_of_x509_basicConstraints_extValue_payload isCA) )

noextract inline_for_extraction
let len_of_x509_basicConstraints_extValue
  (isCA: bool)
: Tot ( if isCA then
         ( (pathLen: datatype_of_asn1_type INTEGER)
           -> Tot (len: asn1_value_int32_of_type OCTET_STRING
                        { v len == length_of_x509_basicConstraints_extValue true pathLen }) )
        else
        ( len: asn1_value_int32_of_type OCTET_STRING
               { v len == length_of_x509_basicConstraints_extValue isCA } ) )
= if isCA then
  ( fun (pathLen: datatype_of_asn1_type INTEGER) ->
      len_of_TLV
        (SEQUENCE)
        (len_of_x509_basicConstraints_extValue_payload true pathLen) )
  else
  ( len_of_TLV
      (SEQUENCE)
      (len_of_x509_basicConstraints_extValue_payload isCA) )

let lemma_serialize_x509_basicConstraints_extValue_size_exact
  (isCA: bool)
  (x: x509_basicConstraints_extValue_t isCA)
: Lemma (
  lemma_serialize_x509_basicConstraints_extValue_unfold isCA x;
  lemma_serialize_x509_basicConstraints_extValue_size isCA x;
    lemma_serialize_x509_basicConstraints_extValue_payload_size isCA x;
  if isCA then
  ( let x = x <: asn1_boolean_true_t `tuple2` datatype_of_asn1_type INTEGER in
    length_of_opaque_serialization (serialize_x509_basicConstraints_extValue isCA) x
    == length_of_x509_basicConstraints_extValue true (snd x) )
  else
  ( length_of_opaque_serialization (serialize_x509_basicConstraints_extValue isCA) x
    == length_of_x509_basicConstraints_extValue false )
)
= lemma_serialize_x509_basicConstraints_extValue_unfold isCA x;
  lemma_serialize_x509_basicConstraints_extValue_size isCA x;
    lemma_serialize_x509_basicConstraints_extValue_payload_size isCA x

(* ext *)

noextract inline_for_extraction
let x509_basicConstraints_t
  (isCA: bool)
: Type
= x509_extension_t
  (**) (OID_BASIC_CONSTRAINTS)
  (**) (serialize_x509_basicConstraints_extValue isCA)

let parse_x509_basicConstraints
  (isCA: bool)
: parser parse_x509_extension_kind (x509_basicConstraints_t isCA)
= x509_basicConstraints_t isCA
  `coerce_parser`
  parse_x509_extension
  (**) (OID_BASIC_CONSTRAINTS)
  (**) (serialize_x509_basicConstraints_extValue isCA)

let serialize_x509_basicConstraints
  (isCA: bool)
: serializer (parse_x509_basicConstraints isCA)
= coerce_parser_serializer
    (parse_x509_basicConstraints isCA)
    (serialize_x509_extension
    (**) (OID_BASIC_CONSTRAINTS)
    (**) (serialize_x509_basicConstraints_extValue isCA))
    ()

noextract inline_for_extraction
let serialize32_x509_basicConstraints_backwards
  (isCA: bool)
: serializer32_backwards (serialize_x509_basicConstraints isCA)
= coerce_serializer32_backwards
    (_)
    (serialize32_x509_extension_backwards
    (**) (OID_BASIC_CONSTRAINTS)
    (**) (serialize32_x509_basicConstraints_extValue_backwards isCA))
    ()

let lemma_serialize_x509_basicConstraints_unfold
  (isCA: bool)
  (x: x509_basicConstraints_t isCA)
: Lemma ( predicate_serialize_x509_extension_unfold
          (**) (OID_BASIC_CONSTRAINTS)
          (**) (serialize_x509_basicConstraints_extValue isCA)
          (**) (x) )
= lemma_serialize_x509_extension_unfold
  (**) (OID_BASIC_CONSTRAINTS)
  (**) (serialize_x509_basicConstraints_extValue isCA)
  (**) (x)

let lemma_serialize_x509_basicConstraints_size
  (isCA: bool)
  (x: x509_basicConstraints_t isCA)
: Lemma ( predicate_serialize_x509_extension_size
          (**) (OID_BASIC_CONSTRAINTS)
          (**) (serialize_x509_basicConstraints_extValue isCA)
          (**) (x) )
= lemma_serialize_x509_extension_size
  (**) (OID_BASIC_CONSTRAINTS)
  (**) (serialize_x509_basicConstraints_extValue isCA)
  (**) (x)

let length_of_x509_basicConstraints
  (isCA: bool)
: GTot ( if isCA then
         ( datatype_of_asn1_type INTEGER -> GTot (asn1_TLV_length_of_type SEQUENCE) )
         else
         ( asn1_TLV_length_of_type SEQUENCE ) )
= if isCA then
  ( fun (pathLen: datatype_of_asn1_type INTEGER) ->
      let x: x509_basicConstraints_extValue_payload_t isCA = (asn1_boolean_true, pathLen) in
      lemma_serialize_x509_basicConstraints_extValue_size_exact isCA x;
      lemma_serialize_x509_basicConstraints_extValue_payload_size isCA x;
      length_of_x509_extension
        (OID_BASIC_CONSTRAINTS)
        (serialize_x509_basicConstraints_extValue isCA)
        (x <: x509_basicConstraints_extValue_t isCA)
        (length_of_x509_basicConstraints_extValue true pathLen) )
  else
  ( let x: x509_basicConstraints_extValue_payload_t isCA = (asn1_boolean_false) in
    lemma_serialize_x509_basicConstraints_extValue_size_exact isCA x;
    lemma_serialize_x509_basicConstraints_extValue_payload_size isCA x;
    length_of_x509_extension
      (OID_BASIC_CONSTRAINTS)
      (serialize_x509_basicConstraints_extValue isCA)
      (x <: x509_basicConstraints_extValue_t isCA)
      (length_of_x509_basicConstraints_extValue false) )

noextract inline_for_extraction
let len_of_x509_basicConstraints
  (isCA: bool)
: Tot ( if isCA then
         ( (pathLen: datatype_of_asn1_type INTEGER)
           -> Tot (len: asn1_TLV_int32_of_type SEQUENCE
                        { v len == length_of_x509_basicConstraints true pathLen }) )
        else
        ( len: asn1_TLV_int32_of_type SEQUENCE
               { v len == length_of_x509_basicConstraints isCA } ) )
= if isCA then
  ( fun (pathLen: datatype_of_asn1_type INTEGER) ->
      let x: x509_basicConstraints_extValue_payload_t isCA = (asn1_boolean_true, pathLen) in
      lemma_serialize_x509_basicConstraints_extValue_size_exact isCA x;
      lemma_serialize_x509_basicConstraints_extValue_payload_size isCA x;
      len_of_x509_extension
        (OID_BASIC_CONSTRAINTS)
        (serialize_x509_basicConstraints_extValue isCA)
        ((asn1_boolean_true, pathLen) <: x509_basicConstraints_extValue_payload_t isCA)
        (len_of_x509_basicConstraints_extValue true pathLen) )
  else
  ( let x: x509_basicConstraints_extValue_payload_t isCA = (asn1_boolean_false) in
    lemma_serialize_x509_basicConstraints_extValue_size_exact isCA x;
    lemma_serialize_x509_basicConstraints_extValue_payload_size isCA x;
    len_of_x509_extension
      (OID_BASIC_CONSTRAINTS)
      (serialize_x509_basicConstraints_extValue isCA)
      (x <: x509_basicConstraints_extValue_t isCA)
      (len_of_x509_basicConstraints_extValue false) )

let lemma_serialize_x509_basicConstraints_size_exact
  (isCA: bool)
  (ext: x509_basicConstraints_t isCA)
: Lemma (
  length_of_opaque_serialization (serialize_x509_basicConstraints isCA) ext ==
  ( if isCA then
    ( let x = snd ext <: asn1_boolean_true_t `tuple2` datatype_of_asn1_type INTEGER in
      length_of_x509_basicConstraints true (snd x) )
    else
    ( length_of_x509_basicConstraints false ) )
)
= if isCA then
  ( lemma_serialize_x509_basicConstraints_extValue_size_exact isCA (snd ext);
    lemma_serialize_x509_basicConstraints_extValue_payload_size isCA (snd ext);
    lemma_serialize_x509_extension_size_exact
      (OID_BASIC_CONSTRAINTS)
      (serialize_x509_basicConstraints_extValue isCA)
      (ext)
      (length_of_x509_basicConstraints_extValue true (snd (snd ext <: x509_basicConstraints_extValue_payload_t true))) )
  else
  ( lemma_serialize_x509_basicConstraints_extValue_size_exact isCA (snd ext);
    lemma_serialize_x509_basicConstraints_extValue_payload_size isCA (snd ext);
    lemma_serialize_x509_extension_size_exact
      (OID_BASIC_CONSTRAINTS)
      (serialize_x509_basicConstraints_extValue isCA)
      (ext)
      (length_of_x509_basicConstraints_extValue false) )

let x509_get_basicConstraints_isCA
  (isCA: bool { isCA == true })
  (criticality: datatype_of_asn1_type BOOLEAN)
  (pathLen: datatype_of_asn1_type INTEGER)
: Tot (x509_basicConstraints_t isCA)
= let extValue_payload: x509_basicConstraints_extValue_payload_t isCA = ((isCA <: asn1_boolean_true_t), pathLen) in
  (* Prf *) lemma_serialize_x509_basicConstraints_extValue_payload_size isCA extValue_payload;

  let extValue: x509_basicConstraints_extValue_t isCA = extValue_payload in
  (* Prf *) lemma_serialize_x509_basicConstraints_extValue_size_exact isCA extValue;

  let ext: x509_basicConstraints_t isCA = x509_get_extension
                                            (OID_BASIC_CONSTRAINTS)
                                            (serialize_x509_basicConstraints_extValue isCA)
                                            (extValue)
                                            (len_of_x509_basicConstraints_extValue true pathLen)
                                            (criticality)
                                            in
  (* return *) ext

noextract inline_for_extraction
let x509_get_basicConstraints_isNotCA
  (isCA: bool { isCA == false })
  (criticality: datatype_of_asn1_type BOOLEAN)
: Tot (x509_basicConstraints_t isCA)
= let extValue_payload: x509_basicConstraints_extValue_payload_t isCA = isCA <: asn1_boolean_false_t in
  (* Prf *) lemma_serialize_x509_basicConstraints_extValue_payload_size isCA extValue_payload;

  let extValue: x509_basicConstraints_extValue_t isCA = extValue_payload in
  (* Prf *) lemma_serialize_x509_basicConstraints_extValue_size_exact isCA extValue;

  let ext: x509_basicConstraints_t isCA = x509_get_extension
                                            (OID_BASIC_CONSTRAINTS)
                                            (Ghost.hide (serialize_x509_basicConstraints_extValue isCA))
                                            (extValue)
                                            (len_of_x509_basicConstraints_extValue isCA)
                                            (criticality)
                                            in
  (* return *) ext

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
