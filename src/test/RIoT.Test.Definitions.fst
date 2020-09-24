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

#set-options "--z3rlimit 64 --fuel 4 --ifuel 0"

let aliasKeyCrt_version: x509_version_t = normalize_term x509_version_3

(* AliasKeyTBS SerialNumber *)
let aliasKeyCrt_serialNumber_len = 2ul
noextract inline_for_extraction let aliasKeyCrt_serialNumber_list
: List.llist byte_pub (v aliasKeyCrt_serialNumber_len)
= [0x01uy; 0x03uy]
let aliasKeyCrt_serialNumber_buf = IB.igcmalloc_of_list HS.root aliasKeyCrt_serialNumber_list

// let aliasKeyCrt_serialNumber: x509_serialNumber_t
// = normalize_term ([@inline_let] let x: big_integer_as_octet_string_t = (|1ul, B32.create 1ul 1uy|) in
//   assert_norm (filter_x509_serialNumber x);
//   x)


(* AliasKeyTBS Names *)
let aliasKeyCrt_s_common_len = 2ul
noextract inline_for_extraction let aliasKeyCrt_s_common_list
: List.llist byte_pub (v aliasKeyCrt_s_common_len)
= [0x01uy; 0x03uy]
let aliasKeyCrt_s_common_buf = IB.igcmalloc_of_list HS.root aliasKeyCrt_s_common_list

let aliasKeyCrt_s_org_len = 2ul
noextract inline_for_extraction let aliasKeyCrt_s_org_list
: List.llist byte_pub (v aliasKeyCrt_s_org_len)
= [0x01uy; 0x03uy]
let aliasKeyCrt_s_org_buf = IB.igcmalloc_of_list HS.root aliasKeyCrt_s_org_list

let aliasKeyCrt_s_country_len = 2ul
noextract inline_for_extraction let aliasKeyCrt_s_country_list
: List.llist byte_pub (v aliasKeyCrt_s_country_len)
= [0x01uy; 0x03uy]
let aliasKeyCrt_s_country_buf = IB.igcmalloc_of_list HS.root aliasKeyCrt_s_country_list

let aliasKeyCrt_i_common_len = 2ul
noextract inline_for_extraction let aliasKeyCrt_i_common_list
: List.llist byte_pub (v aliasKeyCrt_i_common_len)
= [0x01uy; 0x03uy]
let aliasKeyCrt_i_common_buf = IB.igcmalloc_of_list HS.root aliasKeyCrt_i_common_list

let aliasKeyCrt_i_org_len = 2ul
noextract inline_for_extraction let aliasKeyCrt_i_org_list
: List.llist byte_pub (v aliasKeyCrt_i_org_len)
= [0x01uy; 0x03uy]
let aliasKeyCrt_i_org_buf = IB.igcmalloc_of_list HS.root aliasKeyCrt_i_org_list

let aliasKeyCrt_i_country_len = 2ul
noextract inline_for_extraction let aliasKeyCrt_i_country_list
: List.llist byte_pub (v aliasKeyCrt_i_country_len)
= [0x01uy; 0x03uy]
let aliasKeyCrt_i_country_buf = IB.igcmalloc_of_list HS.root aliasKeyCrt_i_country_list

// let s_common: x509_RDN_x520_attribute_string_t COMMON_NAME IA5_STRING
// = normalize_term (asn1_get_character_string #IA5_STRING 2ul (B32.create 2ul 1uy))

// let s_org: x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING
// = normalize_term (asn1_get_character_string #IA5_STRING 2ul (B32.create 2ul 0uy))

// let s_country: x509_RDN_x520_attribute_string_t COMMON_NAME PRINTABLE_STRING
// = normalize_term (asn1_get_character_string #PRINTABLE_STRING 2ul (B32.create 2ul 0x41uy))

// let notBefore: datatype_of_asn1_type Generalized_Time
// = x509_validity_notAfter_default

// let notAfter: datatype_of_asn1_type Generalized_Time
// = x509_validity_notAfter_default

// let aliasKeyCrt_keyID: datatype_of_asn1_type OCTET_STRING
// = normalize_term (|1ul, B32.create 1ul 1uy|)
