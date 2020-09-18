(* NOTE: Separating this module because verification
         with RIoT.* loaded becomes expensive *)
module RIoT.Test.Definitions

open LowStar.Comment
open LowStar.Printf
module Fail = LowStar.Failure
module B = LowStar.Buffer
module IB = LowStar.ImmutableBuffer
module HS  = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B32 = FStar.Bytes

open Lib.IntTypes
open Spec.Hash.Definitions
open Hacl.Hash.Definitions

open ASN1.Spec
open ASN1.Low
open X509

// open RIoT.X509
open RIoT.Base
// open RIoT.Declassify
// open RIoT.Helpers
// open RIoT.Spec
// open RIoT.Impl
// open RIoT.Core

module Ed25519 = Hacl.Ed25519

#set-options "--z3rlimit 64 --fuel 0 --ifuel 0"

let aliasKeyCrt_version: x509_version_t = normalize_term x509_version_3
let aliasKeyCrt_serialNumber: x509_serialNumber_t
= normalize_term ([@inline_let] let x: big_integer_as_octet_string_t = (|1ul, B32.create 1ul 1uy|) in
  assert_norm (filter_x509_serialNumber x);
  x)

let s_common: x509_RDN_x520_attribute_string_t COMMON_NAME IA5_STRING
= normalize_term (asn1_get_character_string #IA5_STRING 2ul (B32.create 2ul 1uy))

let s_org: x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING
= normalize_term (asn1_get_character_string #IA5_STRING 2ul (B32.create 2ul 0uy))

let s_country: x509_RDN_x520_attribute_string_t COMMON_NAME PRINTABLE_STRING
= normalize_term (asn1_get_character_string #PRINTABLE_STRING 2ul (B32.create 2ul 0x41uy))

let notBefore: datatype_of_asn1_type Generalized_Time
= normalize_term (B32.create 13ul 0uy)

let notAfter: datatype_of_asn1_type Generalized_Time
= normalize_term (B32.create 13ul 0uy)

let aliasKeyCrt_keyID: datatype_of_asn1_type OCTET_STRING
= normalize_term (|1ul, B32.create 1ul 1uy|)
