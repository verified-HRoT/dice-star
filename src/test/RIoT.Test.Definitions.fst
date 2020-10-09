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

open RIoT.Base
open RIoT.X509.Base
open RIoT.Declassify
open RIoT.Helpers
// open RIoT.Spec
// open RIoT.Impl
// open RIoT.Core

module Ed25519 = Hacl.Ed25519

#set-options "--z3rlimit 64 --fuel 4 --ifuel 0 --using_facts_from '* -FStar.Tactics -FStar.Reflection'"

let aliasKeyCrt_version: x509_version_t = normalize_term x509_version_3

(* AliasKeyTBS SerialNumber *)
let aliasKeyCrt_serialNumber_len = 2ul
noextract inline_for_extraction let aliasKeyCrt_serialNumber_list
: l: List.llist byte_pub (v aliasKeyCrt_serialNumber_len)
  { valid_big_integer_as_octet_string aliasKeyCrt_serialNumber_len (B32.hide (Seq.createL l)) /\
    filter_x509_serialNumber (asn1_get_big_integer_as_octet_string aliasKeyCrt_serialNumber_len (B32.hide (Seq.createL l))) }
= [0x01uy; 0x03uy]
let aliasKeyCrt_serialNumber_buf = IB.igcmalloc_of_list HS.root aliasKeyCrt_serialNumber_list

(* AliasKeyTBS Names *)
let aliasKeyCrt_s_common_len = 2ul
noextract inline_for_extraction let aliasKeyCrt_s_common_list
: character_string_llist IA5_STRING aliasKeyCrt_s_common_len
= [0x01uy; 0x03uy]
let aliasKeyCrt_s_common_buf = IB.igcmalloc_of_list HS.root aliasKeyCrt_s_common_list

let aliasKeyCrt_s_org_len = 2ul
noextract inline_for_extraction let aliasKeyCrt_s_org_list
: character_string_llist IA5_STRING aliasKeyCrt_s_org_len
= [0x01uy; 0x03uy]
let aliasKeyCrt_s_org_buf = IB.igcmalloc_of_list HS.root aliasKeyCrt_s_org_list

let aliasKeyCrt_s_country_len = 2ul
noextract inline_for_extraction let aliasKeyCrt_s_country_list
: character_string_llist PRINTABLE_STRING aliasKeyCrt_s_country_len
= [0x41uy; 0x42uy]
let aliasKeyCrt_s_country_buf = IB.igcmalloc_of_list HS.root aliasKeyCrt_s_country_list

let aliasKeyCrt_i_common_len = 2ul
noextract inline_for_extraction let aliasKeyCrt_i_common_list
: character_string_llist IA5_STRING aliasKeyCrt_i_common_len
= [0x01uy; 0x03uy]
let aliasKeyCrt_i_common_buf = IB.igcmalloc_of_list HS.root aliasKeyCrt_i_common_list

let aliasKeyCrt_i_org_len = 2ul
noextract inline_for_extraction let aliasKeyCrt_i_org_list
: character_string_llist IA5_STRING aliasKeyCrt_i_org_len
= [0x01uy; 0x03uy]
let aliasKeyCrt_i_org_buf = IB.igcmalloc_of_list HS.root aliasKeyCrt_i_org_list

let aliasKeyCrt_i_country_len = 2ul
noextract inline_for_extraction let aliasKeyCrt_i_country_list
: character_string_llist PRINTABLE_STRING aliasKeyCrt_i_country_len
= [0x41uy; 0x42uy]
let aliasKeyCrt_i_country_buf = IB.igcmalloc_of_list HS.root aliasKeyCrt_i_country_list

(* DeviceID CSR *)
let deviceIDCSR_s_common_len = 2ul
noextract inline_for_extraction let deviceIDCSR_s_common_list
: character_string_llist IA5_STRING deviceIDCSR_s_common_len
= [0x01uy; 0x03uy]
let deviceIDCSR_s_common_buf = IB.igcmalloc_of_list HS.root deviceIDCSR_s_common_list

let deviceIDCSR_s_org_len = 2ul
noextract inline_for_extraction let deviceIDCSR_s_org_list
: character_string_llist IA5_STRING deviceIDCSR_s_org_len
= [0x01uy; 0x03uy]
let deviceIDCSR_s_org_buf = IB.igcmalloc_of_list HS.root deviceIDCSR_s_org_list

let deviceIDCSR_s_country_len = 2ul
noextract inline_for_extraction let deviceIDCSR_s_country_list
: character_string_llist PRINTABLE_STRING deviceIDCSR_s_country_len
= [0x41uy; 0x42uy]
let deviceIDCSR_s_country_buf = IB.igcmalloc_of_list HS.root deviceIDCSR_s_country_list

unfold inline_for_extraction
let deviceIDCSR_keyUsage = normalize_term aliasKeyCrt_key_usage

#set-options "--z3rlimit 64 --fuel 0 --ifuel 0"
inline_for_extraction
let riot_get_deviceIDCSR_ingredients ()
: HST.Stack deviceIDCSR_ingredients_t
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> B.modifies B.loc_none h0 h1)
= let ku: key_usage_payload_t = deviceIDCSR_keyUsage in

  let deviceIDCSR_version: x509_version_t = x509_version_3 in

  IB.recall deviceIDCSR_s_common_buf;
  IB.recall_contents deviceIDCSR_s_common_buf (Seq.createL deviceIDCSR_s_common_list);
  let deviceIDCSR_s_common: x509_RDN_x520_attribute_string_t COMMON_NAME IA5_STRING =
    normalize_term ( asn1_get_character_string
                       #IA5_STRING
                       deviceIDCSR_s_common_len
                       (B32.of_buffer deviceIDCSR_s_common_len deviceIDCSR_s_common_buf) ) in

  IB.recall deviceIDCSR_s_org_buf;
  IB.recall_contents deviceIDCSR_s_org_buf (Seq.createL deviceIDCSR_s_org_list);
  let deviceIDCSR_s_org: x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING =
    normalize_term ( asn1_get_character_string
                       #IA5_STRING
                       deviceIDCSR_s_org_len
                       (B32.of_buffer deviceIDCSR_s_org_len deviceIDCSR_s_org_buf) ) in

  IB.recall deviceIDCSR_s_country_buf;
  IB.recall_contents deviceIDCSR_s_country_buf (Seq.createL deviceIDCSR_s_country_list);
  let deviceIDCSR_s_country: x509_RDN_x520_attribute_string_t COUNTRY PRINTABLE_STRING =
    normalize_term ( asn1_get_character_string
                       #PRINTABLE_STRING
                       deviceIDCSR_s_country_len
                       (B32.of_buffer deviceIDCSR_s_country_len deviceIDCSR_s_country_buf) ) in

  let deviceIDCSR_ingredients: deviceIDCSR_ingredients_t = {
    deviceIDCSR_ku        = ku;
    deviceIDCSR_version   = deviceIDCSR_version;
    deviceIDCSR_s_common  = deviceIDCSR_s_common;
    deviceIDCSR_s_org     = deviceIDCSR_s_org;
    deviceIDCSR_s_country = deviceIDCSR_s_country
  } in

  deviceIDCSR_ingredients

inline_for_extraction
let riot_get_aliasKeyCRT_ingredients ()
: HST.Stack aliasKeyCRT_ingredients_t
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> B.modifies B.loc_none h0 h1)
= let ku: key_usage_payload_t = deviceIDCSR_keyUsage in

  let riot_version: datatype_of_asn1_type INTEGER = 1l in

  IB.recall aliasKeyCrt_serialNumber_buf;
  IB.recall_contents aliasKeyCrt_serialNumber_buf (Seq.createL aliasKeyCrt_serialNumber_list);
  let aliasKeyCrt_serialNumber: x509_serialNumber_t =
    x509_get_serialNumber
      (aliasKeyCrt_serialNumber_len)
      (B32.of_buffer aliasKeyCrt_serialNumber_len aliasKeyCrt_serialNumber_buf) in

  comment "AliasKey Crt Subject Names";
  IB.recall aliasKeyCrt_s_common_buf;
  IB.recall_contents aliasKeyCrt_s_common_buf (Seq.createL aliasKeyCrt_s_common_list);
  let aliasKeyCrt_s_common: x509_RDN_x520_attribute_string_t COMMON_NAME IA5_STRING =
    normalize_term ( asn1_get_character_string
                       #IA5_STRING
                       aliasKeyCrt_s_common_len
                       (B32.of_buffer aliasKeyCrt_s_common_len aliasKeyCrt_s_common_buf) ) in

  IB.recall aliasKeyCrt_s_org_buf;
  IB.recall_contents aliasKeyCrt_s_org_buf (Seq.createL aliasKeyCrt_s_org_list);
  let aliasKeyCrt_s_org: x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING =
    normalize_term ( asn1_get_character_string
                       #IA5_STRING
                       aliasKeyCrt_s_org_len
                       (B32.of_buffer aliasKeyCrt_s_org_len aliasKeyCrt_s_org_buf) ) in

  IB.recall aliasKeyCrt_s_country_buf;
  IB.recall_contents aliasKeyCrt_s_country_buf (Seq.createL aliasKeyCrt_s_country_list);
  let aliasKeyCrt_s_country: x509_RDN_x520_attribute_string_t COUNTRY PRINTABLE_STRING =
    normalize_term ( asn1_get_character_string
                       #PRINTABLE_STRING
                       aliasKeyCrt_s_country_len
                       (B32.of_buffer aliasKeyCrt_s_country_len aliasKeyCrt_s_country_buf) ) in

  comment "AliasKey Crt Issuer Names";
  IB.recall aliasKeyCrt_i_common_buf;
  IB.recall_contents aliasKeyCrt_i_common_buf (Seq.createL aliasKeyCrt_i_common_list);
  let aliasKeyCrt_i_common: x509_RDN_x520_attribute_string_t COMMON_NAME IA5_STRING =
    normalize_term ( asn1_get_character_string
                       #IA5_STRING
                       aliasKeyCrt_i_common_len
                       (B32.of_buffer aliasKeyCrt_i_common_len aliasKeyCrt_i_common_buf) ) in

  IB.recall aliasKeyCrt_i_org_buf;
  IB.recall_contents aliasKeyCrt_i_org_buf (Seq.createL aliasKeyCrt_i_org_list);
  let aliasKeyCrt_i_org: x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING =
    normalize_term ( asn1_get_character_string
                       #IA5_STRING
                       aliasKeyCrt_i_org_len
                       (B32.of_buffer aliasKeyCrt_i_org_len aliasKeyCrt_i_org_buf) ) in

  IB.recall aliasKeyCrt_i_country_buf;
  IB.recall_contents aliasKeyCrt_i_country_buf (Seq.createL aliasKeyCrt_i_country_list);
  let aliasKeyCrt_i_country: x509_RDN_x520_attribute_string_t COUNTRY PRINTABLE_STRING =
    normalize_term ( asn1_get_character_string
                       #PRINTABLE_STRING
                       aliasKeyCrt_i_country_len
                       (B32.of_buffer aliasKeyCrt_i_country_len aliasKeyCrt_i_country_buf) ) in

  IB.recall x509_validity_notAfter_default_buffer;
  IB.recall_contents x509_validity_notAfter_default_buffer asn1_generalized_time_for_x509_validity_notAfter_default_seq;
  let notBefore: datatype_of_asn1_type Generalized_Time = B32.of_buffer 15ul x509_validity_notAfter_default_buffer in
  let notAfter : datatype_of_asn1_type Generalized_Time = B32.of_buffer 15ul x509_validity_notAfter_default_buffer in

  let aliasKeyCRT_ingredients: aliasKeyCRT_ingredients_t = {
    aliasKeyCrt_version      = aliasKeyCrt_version;
    aliasKeyCrt_serialNumber = aliasKeyCrt_serialNumber;
    aliasKeyCrt_i_common     = aliasKeyCrt_i_common;
    aliasKeyCrt_i_org        = aliasKeyCrt_i_org;
    aliasKeyCrt_i_country    = aliasKeyCrt_i_country;
    aliasKeyCrt_notBefore    = notBefore;
    aliasKeyCrt_notAfter     = notAfter;
    aliasKeyCrt_s_common     = aliasKeyCrt_s_common;
    aliasKeyCrt_s_org        = aliasKeyCrt_s_org;
    aliasKeyCrt_s_country    = aliasKeyCrt_s_country;
    aliasKeyCrt_ku           = ku;
    aliasKeyCrt_riot_version = riot_version
  } in

  aliasKeyCRT_ingredients

[@@ "opaque_to_smt"]
inline_for_extraction
let dump_riot
  (deviceID_pub : B.lbuffer byte_pub 32)
  (aliasKey_pub : B.lbuffer byte_pub 32)
  (aliasKey_priv: B.lbuffer byte_sec 32)
  (deviceIDCSR_len: UInt32.t)
  (deviceIDCSR_buf: B.lbuffer byte_pub (v deviceIDCSR_len))
  (aliasKeyCRT_len: UInt32.t)
  (aliasKeyCRT_buf: B.lbuffer byte_pub (v aliasKeyCRT_len))
: HST.Stack unit
  (requires fun h ->
    B.all_live h [B.buf deviceID_pub; B.buf aliasKey_pub; B.buf aliasKey_priv; B.buf deviceIDCSR_buf; B.buf aliasKeyCRT_buf])
  (ensures fun h0 _ h1 ->
    B.modifies B.loc_none h0 h1)
= HST.push_frame ();
  let aliasKey_priv_pub: B.lbuffer byte_pub 32 = B.alloca 0x00uy 32ul in
  declassify_secret_buffer 32ul aliasKey_priv aliasKey_priv_pub;

  write_out "DeviceIDPublicKey.hex"  aliasKey_pub 32ul;
  write_out "AliasKeyPublicKey.hex"  aliasKey_pub 32ul;
  write_out "AliasKeyPrivateKey.hex" aliasKey_priv_pub 32ul;
  write_out "DeviceIDCSR.hex" deviceIDCSR_buf deviceIDCSR_len;
  write_out "AliasKeyCrt.hex" aliasKeyCRT_buf aliasKeyCRT_len;
  HST.pop_frame ()
