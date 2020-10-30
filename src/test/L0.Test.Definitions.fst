(* NOTE: Separating this module because verification
         with L0.* loaded becomes expensive *)
module L0.Test.Definitions

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

open L0.Base
open L0.X509.Base
open L0.Declassify
open L0.Helpers
// open L0.Spec
// open L0.Impl
// open L0.Core

module Ed25519 = Hacl.Ed25519

#set-options "--z3rlimit 64 --fuel 0 --ifuel 0 --using_facts_from '* -FStar.Tactics -FStar.Reflection'"

let aliasKeyCrt_version: x509_version_t = normalize_term x509_version_3

#push-options "--fuel 9"
(* AliasKeyTBS SerialNumber *)
let aliasKeyCrt_serialNumber_len = 8ul
noextract inline_for_extraction let aliasKeyCrt_serialNumber_list
: l: List.llist byte_pub (v aliasKeyCrt_serialNumber_len)
  { valid_big_integer_as_octet_string aliasKeyCrt_serialNumber_len (B32.hide (Seq.createL l)) /\
    filter_x509_serialNumber (asn1_get_big_integer_as_octet_string aliasKeyCrt_serialNumber_len (B32.hide (Seq.createL l))) }
= [0x27uy; 0x48uy; 0x4Buy; 0xD6uy;
   0xF2uy; 0x10uy; 0xB4uy; 0xDAuy]
let aliasKeyCrt_serialNumber_buf = IB.igcmalloc_of_list HS.root aliasKeyCrt_serialNumber_list
#pop-options

(* AliasKeyTBS Names *)
(* Common Name in IA5 (ASCII): `Platform Identity` *)
#push-options "--z3rlimit 50 --fuel 0"
let aliasKeyCrt_s_common_len = 17ul
noextract inline_for_extraction let aliasKeyCrt_s_common_list
: character_string_llist IA5_STRING aliasKeyCrt_s_common_len
= [@ inline_let]
  let l = [0x50uy; 0x6cuy; 0x61uy; 0x74uy;
           0x66uy; 0x6fuy; 0x72uy; 0x6duy;
           0x20uy; 0x49uy; 0x64uy; 0x65uy;
           0x6euy; 0x74uy; 0x69uy; 0x74uy;
           0x79uy] in
  assert_norm ( List.length l == 17 /\ Seq.length (Seq.createL l) == 17);
  assert ( l == Seq.seq_to_list (Seq.createL l) );
  Seq.lemma_index_is_nth (Seq.createL l) 1;
  Seq.lemma_index_is_nth (Seq.createL l) 2;
  Seq.lemma_index_is_nth (Seq.createL l) 3;
  Seq.lemma_index_is_nth (Seq.createL l) 4;
  Seq.lemma_index_is_nth (Seq.createL l) 5;
  Seq.lemma_index_is_nth (Seq.createL l) 6;
  Seq.lemma_index_is_nth (Seq.createL l) 7;
  Seq.lemma_index_is_nth (Seq.createL l) 8;
  Seq.lemma_index_is_nth (Seq.createL l) 9;
  Seq.lemma_index_is_nth (Seq.createL l) 10;
  Seq.lemma_index_is_nth (Seq.createL l) 11;
  Seq.lemma_index_is_nth (Seq.createL l) 12;
  Seq.lemma_index_is_nth (Seq.createL l) 13;
  Seq.lemma_index_is_nth (Seq.createL l) 14;
  Seq.lemma_index_is_nth (Seq.createL l) 15;
  Seq.lemma_index_is_nth (Seq.createL l) 16;
  assert_norm ( l `List.Tot.index` 0  == 0x50uy /\
                l `List.Tot.index` 1  == 0x6cuy /\
                l `List.Tot.index` 2  == 0x61uy /\
                l `List.Tot.index` 3  == 0x74uy /\
                l `List.Tot.index` 4  == 0x66uy /\
                l `List.Tot.index` 5  == 0x6fuy /\
                l `List.Tot.index` 6  == 0x72uy /\
                l `List.Tot.index` 7  == 0x6duy /\
                l `List.Tot.index` 8  == 0x20uy /\
                l `List.Tot.index` 9  == 0x49uy /\
                l `List.Tot.index` 10 == 0x64uy /\
                l `List.Tot.index` 11 == 0x65uy /\
                l `List.Tot.index` 12 == 0x6euy /\
                l `List.Tot.index` 13 == 0x74uy /\
                l `List.Tot.index` 14 == 0x69uy /\
                l `List.Tot.index` 15 == 0x74uy /\
                l `List.Tot.index` 16 == 0x79uy );
  assert ( (Seq.createL l).[0]  == 0x50uy /\ valid_character_string_byte IA5_STRING (Seq.createL l).[0]);
  assert ( (Seq.createL l).[1]  == 0x6cuy /\ valid_character_string_byte IA5_STRING (Seq.createL l).[1]);
  assert ( (Seq.createL l).[2]  == 0x61uy /\ valid_character_string_byte IA5_STRING (Seq.createL l).[2]);
  assert ( (Seq.createL l).[3]  == 0x74uy /\ valid_character_string_byte IA5_STRING (Seq.createL l).[3]);
  assert ( (Seq.createL l).[4]  == 0x66uy /\ valid_character_string_byte IA5_STRING (Seq.createL l).[4]);
  assert ( (Seq.createL l).[5]  == 0x6fuy /\ valid_character_string_byte IA5_STRING (Seq.createL l).[5]);
  assert ( (Seq.createL l).[6]  == 0x72uy /\ valid_character_string_byte IA5_STRING (Seq.createL l).[6]);
  assert ( (Seq.createL l).[7]  == 0x6duy /\ valid_character_string_byte IA5_STRING (Seq.createL l).[7]);
  assert ( (Seq.createL l).[8]  == 0x20uy /\ valid_character_string_byte IA5_STRING (Seq.createL l).[8]);
  assert ( (Seq.createL l).[9]  == 0x49uy /\ valid_character_string_byte IA5_STRING (Seq.createL l).[9]);
  assert ( (Seq.createL l).[10] == 0x64uy /\ valid_character_string_byte IA5_STRING (Seq.createL l).[10]);
  assert ( (Seq.createL l).[11] == 0x65uy /\ valid_character_string_byte IA5_STRING (Seq.createL l).[11]);
  assert ( (Seq.createL l).[12] == 0x6euy /\ valid_character_string_byte IA5_STRING (Seq.createL l).[12]);
  assert ( (Seq.createL l).[13] == 0x74uy /\ valid_character_string_byte IA5_STRING (Seq.createL l).[13]);
  assert ( (Seq.createL l).[14] == 0x69uy /\ valid_character_string_byte IA5_STRING (Seq.createL l).[14]);
  assert ( (Seq.createL l).[15] == 0x74uy /\ valid_character_string_byte IA5_STRING (Seq.createL l).[15]);
  assert ( (Seq.createL l).[16] == 0x79uy /\ valid_character_string_byte IA5_STRING (Seq.createL l).[16]);
  l
let aliasKeyCrt_s_common_buf = IB.igcmalloc_of_list HS.root aliasKeyCrt_s_common_list

#push-options "--fuel 6"
let aliasKeyCrt_s_org_len = 4ul
noextract inline_for_extraction let aliasKeyCrt_s_org_list
: character_string_llist IA5_STRING aliasKeyCrt_s_org_len
= [0x49uy; 0x6euy; 0x63uy; 0x2euy]
let aliasKeyCrt_s_org_buf = IB.igcmalloc_of_list HS.root aliasKeyCrt_s_org_list

let aliasKeyCrt_s_country_len = 2ul
noextract inline_for_extraction let aliasKeyCrt_s_country_list
: character_string_llist PRINTABLE_STRING aliasKeyCrt_s_country_len
= [0x55uy; 0x4Buy]
let aliasKeyCrt_s_country_buf = IB.igcmalloc_of_list HS.root aliasKeyCrt_s_country_list

let aliasKeyCrt_i_common_len = 5ul
noextract inline_for_extraction let aliasKeyCrt_i_common_list
: character_string_llist IA5_STRING aliasKeyCrt_i_common_len
= [0x41uy; 0x6cuy; 0x69uy; 0x61uy; 0x73uy]
let aliasKeyCrt_i_common_buf = IB.igcmalloc_of_list HS.root aliasKeyCrt_i_common_list

let aliasKeyCrt_i_org_len = 4ul
noextract inline_for_extraction let aliasKeyCrt_i_org_list
: character_string_llist IA5_STRING aliasKeyCrt_i_org_len
= [0x49uy; 0x6euy; 0x63uy; 0x2euy]
let aliasKeyCrt_i_org_buf = IB.igcmalloc_of_list HS.root aliasKeyCrt_i_org_list

let aliasKeyCrt_i_country_len = 2ul
noextract inline_for_extraction let aliasKeyCrt_i_country_list
: character_string_llist PRINTABLE_STRING aliasKeyCrt_i_country_len
= [0x55uy; 0x4Buy]
let aliasKeyCrt_i_country_buf = IB.igcmalloc_of_list HS.root aliasKeyCrt_i_country_list
#pop-options

inline_for_extraction
let l0_get_aliasKeyCRT_ingredients ()
: HST.Stack aliasKeyCRT_ingredients_t
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> B.modifies B.loc_none h0 h1)
= let ku: key_usage_payload_t = normalize_term aliasKeyCrt_key_usage in

  let l0_version: datatype_of_asn1_type INTEGER = 1l in

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


  IB.recall x509_validity_notBefore_default_buffer;
  IB.recall_contents x509_validity_notBefore_default_buffer asn1_utc_time_for_x509_validity_notBefore_default_seq;
  let notBefore: datatype_of_asn1_type UTC_TIME = B32.of_buffer 13ul x509_validity_notBefore_default_buffer in

  IB.recall x509_validity_notAfter_default_buffer;
  IB.recall_contents x509_validity_notAfter_default_buffer asn1_generalized_time_for_x509_validity_notAfter_default_seq;
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
    aliasKeyCrt_l0_version = riot_version
  } in

  aliasKeyCRT_ingredients


(* DeviceID CSR *)
(* Common Name in IA5 (ASCII): `Platform Identity` *)
#push-options "--z3rlimit 50 --fuel 0"
let deviceIDCSR_s_common_len = 17ul
noextract inline_for_extraction let deviceIDCSR_s_common_list
: character_string_llist IA5_STRING deviceIDCSR_s_common_len
= [@ inline_let]
  let l = [0x50uy; 0x6cuy; 0x61uy; 0x74uy;
           0x66uy; 0x6fuy; 0x72uy; 0x6duy;
           0x20uy; 0x49uy; 0x64uy; 0x65uy;
           0x6euy; 0x74uy; 0x69uy; 0x74uy;
           0x79uy] in
  assert_norm ( List.length l == 17 /\ Seq.length (Seq.createL l) == 17);
  assert ( l == Seq.seq_to_list (Seq.createL l) );
  Seq.lemma_index_is_nth (Seq.createL l) 1;
  Seq.lemma_index_is_nth (Seq.createL l) 2;
  Seq.lemma_index_is_nth (Seq.createL l) 3;
  Seq.lemma_index_is_nth (Seq.createL l) 4;
  Seq.lemma_index_is_nth (Seq.createL l) 5;
  Seq.lemma_index_is_nth (Seq.createL l) 6;
  Seq.lemma_index_is_nth (Seq.createL l) 7;
  Seq.lemma_index_is_nth (Seq.createL l) 8;
  Seq.lemma_index_is_nth (Seq.createL l) 9;
  Seq.lemma_index_is_nth (Seq.createL l) 10;
  Seq.lemma_index_is_nth (Seq.createL l) 11;
  Seq.lemma_index_is_nth (Seq.createL l) 12;
  Seq.lemma_index_is_nth (Seq.createL l) 13;
  Seq.lemma_index_is_nth (Seq.createL l) 14;
  Seq.lemma_index_is_nth (Seq.createL l) 15;
  Seq.lemma_index_is_nth (Seq.createL l) 16;
  assert_norm ( l `List.Tot.index` 0  == 0x50uy /\
                l `List.Tot.index` 1  == 0x6cuy /\
                l `List.Tot.index` 2  == 0x61uy /\
                l `List.Tot.index` 3  == 0x74uy /\
                l `List.Tot.index` 4  == 0x66uy /\
                l `List.Tot.index` 5  == 0x6fuy /\
                l `List.Tot.index` 6  == 0x72uy /\
                l `List.Tot.index` 7  == 0x6duy /\
                l `List.Tot.index` 8  == 0x20uy /\
                l `List.Tot.index` 9  == 0x49uy /\
                l `List.Tot.index` 10 == 0x64uy /\
                l `List.Tot.index` 11 == 0x65uy /\
                l `List.Tot.index` 12 == 0x6euy /\
                l `List.Tot.index` 13 == 0x74uy /\
                l `List.Tot.index` 14 == 0x69uy /\
                l `List.Tot.index` 15 == 0x74uy /\
                l `List.Tot.index` 16 == 0x79uy );
  assert ( (Seq.createL l).[0]  == 0x50uy /\ valid_character_string_byte IA5_STRING (Seq.createL l).[0]);
  assert ( (Seq.createL l).[1]  == 0x6cuy /\ valid_character_string_byte IA5_STRING (Seq.createL l).[1]);
  assert ( (Seq.createL l).[2]  == 0x61uy /\ valid_character_string_byte IA5_STRING (Seq.createL l).[2]);
  assert ( (Seq.createL l).[3]  == 0x74uy /\ valid_character_string_byte IA5_STRING (Seq.createL l).[3]);
  assert ( (Seq.createL l).[4]  == 0x66uy /\ valid_character_string_byte IA5_STRING (Seq.createL l).[4]);
  assert ( (Seq.createL l).[5]  == 0x6fuy /\ valid_character_string_byte IA5_STRING (Seq.createL l).[5]);
  assert ( (Seq.createL l).[6]  == 0x72uy /\ valid_character_string_byte IA5_STRING (Seq.createL l).[6]);
  assert ( (Seq.createL l).[7]  == 0x6duy /\ valid_character_string_byte IA5_STRING (Seq.createL l).[7]);
  assert ( (Seq.createL l).[8]  == 0x20uy /\ valid_character_string_byte IA5_STRING (Seq.createL l).[8]);
  assert ( (Seq.createL l).[9]  == 0x49uy /\ valid_character_string_byte IA5_STRING (Seq.createL l).[9]);
  assert ( (Seq.createL l).[10] == 0x64uy /\ valid_character_string_byte IA5_STRING (Seq.createL l).[10]);
  assert ( (Seq.createL l).[11] == 0x65uy /\ valid_character_string_byte IA5_STRING (Seq.createL l).[11]);
  assert ( (Seq.createL l).[12] == 0x6euy /\ valid_character_string_byte IA5_STRING (Seq.createL l).[12]);
  assert ( (Seq.createL l).[13] == 0x74uy /\ valid_character_string_byte IA5_STRING (Seq.createL l).[13]);
  assert ( (Seq.createL l).[14] == 0x69uy /\ valid_character_string_byte IA5_STRING (Seq.createL l).[14]);
  assert ( (Seq.createL l).[15] == 0x74uy /\ valid_character_string_byte IA5_STRING (Seq.createL l).[15]);
  assert ( (Seq.createL l).[16] == 0x79uy /\ valid_character_string_byte IA5_STRING (Seq.createL l).[16]);
  l
let deviceIDCSR_s_common_buf = IB.igcmalloc_of_list HS.root deviceIDCSR_s_common_list

#push-options "--fuel 6"
let deviceIDCSR_s_org_len = 4ul
noextract inline_for_extraction let deviceIDCSR_s_org_list
: character_string_llist IA5_STRING deviceIDCSR_s_org_len
= [0x49uy; 0x6euy; 0x63uy; 0x2euy]
let deviceIDCSR_s_org_buf = IB.igcmalloc_of_list HS.root deviceIDCSR_s_org_list

let deviceIDCSR_s_country_len = 2ul
noextract inline_for_extraction let deviceIDCSR_s_country_list
: character_string_llist PRINTABLE_STRING deviceIDCSR_s_country_len
= [0x55uy; 0x4Buy]
let deviceIDCSR_s_country_buf = IB.igcmalloc_of_list HS.root deviceIDCSR_s_country_list

unfold inline_for_extraction
let deviceIDCSR_keyUsage = normalize_term aliasKeyCrt_key_usage
#pop-options

#push-options "--z3rlimit 64 --fuel 0 --ifuel 0"
inline_for_extraction
let l0_get_deviceIDCSR_ingredients ()
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

[@@ "opaque_to_smt"]
inline_for_extraction
let dump_l0
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
#pop-options
