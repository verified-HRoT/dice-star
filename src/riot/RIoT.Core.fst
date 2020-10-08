/// Reference: https://github.com/microsoft/RIoT/blob/master/Reference/RIoT/Core/RIoT.cpp
module RIoT.Core

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

open RIoT.X509
open RIoT.Base
open RIoT.Declassify
open RIoT.Helpers
open RIoT.Spec
open RIoT.Impl

module Ed25519 = Hacl.Ed25519

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0 --using_facts_from '* -FStar.Tactics -FStar.Reflection'"

noeq
type deviceIDCSR_ingredients_t = {
  deviceIDCSR_ku: key_usage_payload_t;
  deviceIDCSR_version: datatype_of_asn1_type INTEGER;
  deviceIDCSR_s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING;
  deviceIDCSR_s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING;
  deviceIDCSR_s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING
}

noeq
type aliasKeyCRT_ingredients_t = {
  aliasKeyCrt_version: x509_version_t;
  aliasKeyCrt_serialNumber: x509_serialNumber_t;
  aliasKeyCrt_i_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING;
  aliasKeyCrt_i_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING;
  aliasKeyCrt_i_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING;
  aliasKeyCrt_notBefore: datatype_of_asn1_type Generalized_Time;
  aliasKeyCrt_notAfter : datatype_of_asn1_type Generalized_Time;
  aliasKeyCrt_s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING;
  aliasKeyCrt_s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING;
  aliasKeyCrt_s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING;
  aliasKeyCrt_ku: key_usage_payload_t;
  aliasKeyCrt_riot_version: datatype_of_asn1_type INTEGER;
}

unfold
let deviceIDCRI_pre (x:deviceIDCSR_ingredients_t) =
  True
  // valid_deviceIDCRI_ingredients
  //   x.deviceIDCSR_version x.deviceIDCSR_s_common x.deviceIDCSR_s_org x.deviceIDCSR_s_country x.deviceIDCSR_ku

[@@ "opaque_to_smt"]
unfold noextract
let coerce_asn1_tlv_int32_of_type_to_asn1_int32 (x:asn1_TLV_int32_of_type SEQUENCE)
  : asn1_int32 = x

unfold
let deviceIDCSR_pre (x:deviceIDCSR_ingredients_t{deviceIDCRI_pre x}) (deviceIDCSR_len:UInt32.t) =
  let l = //coerce_asn1_tlv_int32_of_type_to_asn1_int32
    (len_of_deviceIDCRI
      x.deviceIDCSR_version x.deviceIDCSR_s_common x.deviceIDCSR_s_org
      x.deviceIDCSR_s_country) in

  valid_deviceIDCSR_ingredients l /\
  eq2 #nat (v deviceIDCSR_len) (length_of_deviceIDCSR l)

unfold
let aliasKeyCRT_pre (x:aliasKeyCRT_ingredients_t) (aliasKeyCRT_len:UInt32.t) =
  let l = //coerce_asn1_tlv_int32_of_type_to_asn1_int32
    (len_of_aliasKeyTBS
      x.aliasKeyCrt_serialNumber x.aliasKeyCrt_i_common x.aliasKeyCrt_i_org x.aliasKeyCrt_i_country
      x.aliasKeyCrt_s_common x.aliasKeyCrt_s_org x.aliasKeyCrt_s_country
      x.aliasKeyCrt_riot_version) in
  valid_aliasKeyCRT_ingredients l /\
  eq2 #nat (v aliasKeyCRT_len) (length_of_aliasKeyCRT l)

unfold
let riot_pre
  (h: HS.mem)
(* Common Inputs *)
  (cdi : B.lbuffer byte_sec 32)
  (fwid: B.lbuffer byte_sec 32)
  (deviceID_label_len: UInt32.t)
  (deviceID_label: B.lbuffer byte_sec (v deviceID_label_len))
  (aliasKey_label_len: UInt32.t)
  (aliasKey_label: B.lbuffer byte_sec (v aliasKey_label_len))
(* DeviceID CSR Inputs*)
  (deviceIDCSR_ingredients:deviceIDCSR_ingredients_t)
(* AliasKey Crt Inputs*)
  (aliasKeyCRT_ingredients:aliasKeyCRT_ingredients_t)
(* Common Outputs *)
  (aliasKey_pub: B.lbuffer byte_pub 32)
  (aliasKey_priv: B.lbuffer uint8 32)
(* DeviceID CSR Outputs *)
  (deviceIDCSR_len: UInt32.t)
  (deviceIDCSR_buf: B.lbuffer byte_pub (v deviceIDCSR_len))
(* AliasKey Crt Outputs *)
  (aliasKeyCRT_len: UInt32.t)
  (aliasKeyCRT_buf: B.lbuffer byte_pub (v aliasKeyCRT_len))
: Type0
=   B.(all_live h [buf cdi;
                   buf fwid;
                   buf deviceID_label;
                   buf aliasKey_label;
                   buf deviceIDCSR_buf;
                   buf aliasKeyCRT_buf;
                   buf aliasKey_pub;
                   buf aliasKey_priv]) /\
    B.(all_disjoint [loc_buffer cdi;
                     loc_buffer fwid;
                     loc_buffer deviceID_label;
                     loc_buffer aliasKey_label;
                     loc_buffer deviceIDCSR_buf;
                     loc_buffer aliasKeyCRT_buf;
                     loc_buffer aliasKey_pub;
                     loc_buffer aliasKey_priv]) /\
   (* Pre: labels have enough length for HKDF *)
   valid_hkdf_lbl_len deviceID_label_len /\
   valid_hkdf_lbl_len aliasKey_label_len /\

   deviceIDCRI_pre deviceIDCSR_ingredients /\
   deviceIDCSR_pre deviceIDCSR_ingredients deviceIDCSR_len /\
   aliasKeyCRT_pre aliasKeyCRT_ingredients aliasKeyCRT_len

unfold
let aliasKey_post
  (cdi : B.lbuffer byte_sec 32) (fwid: B.lbuffer byte_sec 32)
  (aliasKey_label_len:UInt32.t{valid_hkdf_lbl_len aliasKey_label_len})
  (aliasKey_label: B.lbuffer byte_sec (v aliasKey_label_len))
  (aliasKey_pub: B.lbuffer byte_pub 32)
  (aliasKey_priv: B.lbuffer uint8 32)
  (h0 h1:HS.mem)
 = ((B.as_seq h1 aliasKey_pub  <: lbytes_pub 32),
    (B.as_seq h1 aliasKey_priv <: lbytes_sec 32)) == derive_AliasKey_spec
                                                       (B.as_seq h0 cdi)
                                                       (B.as_seq h0 fwid)
                                                       (aliasKey_label_len)
                                                       (B.as_seq h0 aliasKey_label)

unfold
let deviceIDCSR_post
  (cdi:B.lbuffer byte_sec 32)
  (deviceID_label_len:UInt32.t{valid_hkdf_lbl_len deviceID_label_len})
  (deviceID_label:B.lbuffer byte_sec (v deviceID_label_len))
  (deviceIDCSR_ingredients:deviceIDCSR_ingredients_t)
  (deviceIDCSR_len:UInt32.t{
    deviceIDCRI_pre deviceIDCSR_ingredients /\
    deviceIDCSR_pre deviceIDCSR_ingredients deviceIDCSR_len})
  (deviceIDCSR_buf:B.lbuffer byte_pub (v deviceIDCSR_len))
  (h0 h1:HS.mem)
  = let deviceID_pub_seq, deviceID_priv_seq = derive_DeviceID_spec
                                                (B.as_seq h0 cdi)
                                                (deviceID_label_len)
                                                (B.as_seq h0 deviceID_label) in
    let deviceIDCRI: deviceIDCRI_t = create_deviceIDCRI_spec
      deviceIDCSR_ingredients.deviceIDCSR_version deviceIDCSR_ingredients.deviceIDCSR_s_common
      deviceIDCSR_ingredients.deviceIDCSR_s_org deviceIDCSR_ingredients.deviceIDCSR_s_country
      deviceIDCSR_ingredients.deviceIDCSR_ku deviceID_pub_seq in

    let deviceIDCRI_seq = serialize_deviceIDCRI `serialize` deviceIDCRI in

    let deviceIDCRI_len = coerce_asn1_tlv_int32_of_type_to_asn1_int32
      (len_of_deviceIDCRI
        deviceIDCSR_ingredients.deviceIDCSR_version deviceIDCSR_ingredients.deviceIDCSR_s_common
        deviceIDCSR_ingredients.deviceIDCSR_s_org deviceIDCSR_ingredients.deviceIDCSR_s_country) in

    let (* Prf *) _ = lemma_serialize_deviceIDCRI_size_exact deviceIDCRI in
    let deviceIDCSR: deviceIDCSR_t deviceIDCRI_len = sign_and_finalize_deviceIDCSR_spec
                                                                (deviceID_priv_seq)
                                                                (deviceIDCRI_len)
                                                                (deviceIDCRI_seq) in
    B.as_seq h1 deviceIDCSR_buf == serialize_deviceIDCSR deviceIDCRI_len `serialize` deviceIDCSR

// unfold noextract
// let coerce_asn1_int32_to_size_t (x:asn1_int32) : UInt32.t = x

#push-options "--z3rlimit 100"
unfold
let aliasKeyCRT_post
  (cdi:B.lbuffer byte_sec 32)
  (fwid: B.lbuffer byte_sec 32)
  (deviceID_label_len:UInt32.t{valid_hkdf_lbl_len deviceID_label_len})
  (deviceID_label:B.lbuffer byte_sec (v deviceID_label_len))
  (aliasKeyCRT_ingredients:aliasKeyCRT_ingredients_t)
  (aliasKeyCRT_len:UInt32.t{
    aliasKeyCRT_pre aliasKeyCRT_ingredients aliasKeyCRT_len})
  (aliasKeyCRT_buf: B.lbuffer byte_pub (v aliasKeyCRT_len))
  (aliasKey_pub: B.lbuffer byte_pub 32)
  (h0 h1:HS.mem)
  = let deviceID_pub_seq, deviceID_priv_seq = derive_DeviceID_spec
                                                 (B.as_seq h0 cdi)
                                                 (deviceID_label_len)
                                                 (B.as_seq h0 deviceID_label) in
    let aliasKeyCrt_keyID_seq: lbytes_pub 20 =
      derive_authKeyID_spec (classify_public_bytes deviceID_pub_seq) in
    let aliasKeyTBS = create_aliasKeyTBS_spec
      aliasKeyCRT_ingredients.aliasKeyCrt_version
      aliasKeyCRT_ingredients.aliasKeyCrt_serialNumber
      aliasKeyCRT_ingredients.aliasKeyCrt_i_common
      aliasKeyCRT_ingredients.aliasKeyCrt_i_org
      aliasKeyCRT_ingredients.aliasKeyCrt_i_country
      aliasKeyCRT_ingredients.aliasKeyCrt_notBefore
      aliasKeyCRT_ingredients.aliasKeyCrt_notAfter
      aliasKeyCRT_ingredients.aliasKeyCrt_s_common
      aliasKeyCRT_ingredients.aliasKeyCrt_s_org
      aliasKeyCRT_ingredients.aliasKeyCrt_s_country
      aliasKeyCRT_ingredients.aliasKeyCrt_ku
      aliasKeyCrt_keyID_seq
      aliasKeyCRT_ingredients.aliasKeyCrt_riot_version
      (B.as_seq h0 fwid)
      deviceID_pub_seq
      (B.as_seq h1 aliasKey_pub) in
     let aliasKeyTBS_seq = serialize_aliasKeyTBS `serialize` aliasKeyTBS in
     let aliasKeyTBS_len = //coerce_asn1_tlv_int32_of_type_to_asn1_int32
       (len_of_aliasKeyTBS
         aliasKeyCRT_ingredients.aliasKeyCrt_serialNumber
         aliasKeyCRT_ingredients.aliasKeyCrt_i_common
         aliasKeyCRT_ingredients.aliasKeyCrt_i_org
         aliasKeyCRT_ingredients.aliasKeyCrt_i_country
         aliasKeyCRT_ingredients.aliasKeyCrt_s_common
         aliasKeyCRT_ingredients.aliasKeyCrt_s_org
         aliasKeyCRT_ingredients.aliasKeyCrt_s_country
         aliasKeyCRT_ingredients.aliasKeyCrt_riot_version) in
     let (* Prf *) _ = lemma_serialize_aliasKeyTBS_size_exact aliasKeyTBS in
     assert (Seq.length aliasKeyTBS_seq == v aliasKeyTBS_len); //TODO: help Z3 prove it
     let aliasKeyCRT: aliasKeyCRT_t aliasKeyTBS_len = sign_and_finalize_aliasKeyCRT_spec
                                                                (deviceID_priv_seq)
                                                                (aliasKeyTBS_len)
                                                                (aliasKeyTBS_seq) in
     B.as_seq h1 aliasKeyCRT_buf == serialize_aliasKeyCRT aliasKeyTBS_len `serialize` aliasKeyCRT
#pop-options

unfold
let riot_post
(* Common Inputs *)
  (cdi : B.lbuffer byte_sec 32)
  (fwid: B.lbuffer byte_sec 32)
  (deviceID_label_len: UInt32.t)
  (deviceID_label: B.lbuffer byte_sec (v deviceID_label_len))
  (aliasKey_label_len: UInt32.t)
  (aliasKey_label: B.lbuffer byte_sec (v aliasKey_label_len))
(* DeviceID CSR Inputs*)
  (deviceIDCSR_ingredients:deviceIDCSR_ingredients_t)
(* AliasKey Crt Inputs*)
  (aliasKeyCRT_ingredients:aliasKeyCRT_ingredients_t)
(* Common Outputs *)
  (aliasKey_pub: B.lbuffer byte_pub 32)
  (aliasKey_priv: B.lbuffer uint8 32)
(* DeviceID CSR Outputs *)
  (deviceIDCSR_len: UInt32.t)
  (deviceIDCSR_buf: B.lbuffer byte_pub (v deviceIDCSR_len))
(* AliasKey Crt Outputs *)
  (aliasKeyCRT_len: UInt32.t)
  (aliasKeyCRT_buf: B.lbuffer byte_pub (v aliasKeyCRT_len))
  (h0:HS.mem{
    riot_pre h0 cdi fwid deviceID_label_len deviceID_label
    aliasKey_label_len aliasKey_label deviceIDCSR_ingredients
    aliasKeyCRT_ingredients aliasKey_pub aliasKey_priv
    deviceIDCSR_len deviceIDCSR_buf
    aliasKeyCRT_len aliasKeyCRT_buf})
  (h1:HS.mem)
  : Type0
  =
    B.(modifies (loc_buffer aliasKey_pub    `loc_union`
                 loc_buffer aliasKey_priv   `loc_union`
                 loc_buffer deviceIDCSR_buf `loc_union`
                 loc_buffer aliasKeyCRT_buf) h0 h1) /\

    aliasKey_post cdi fwid aliasKey_label_len aliasKey_label aliasKey_pub aliasKey_priv h0 h1 /\

    deviceIDCSR_post cdi deviceID_label_len deviceID_label
      deviceIDCSR_ingredients deviceIDCSR_len deviceIDCSR_buf h0 h1 /\

    aliasKeyCRT_post cdi fwid deviceID_label_len deviceID_label
      aliasKeyCRT_ingredients aliasKeyCRT_len aliasKeyCRT_buf aliasKey_pub h0 h1 /\
True

module U32 = FStar.UInt32
module U8 = FStar.UInt8
#reset-options
#set-options "--z3rlimit 400 --fuel 0 --ifuel 0"
let riot
(* Common Inputs *)
  (cdi : B.lbuffer byte_sec 32)
  (fwid: B.lbuffer byte_sec 32)
  (deviceID_label_len: UInt32.t)
  (deviceID_label: B.lbuffer byte_sec (v deviceID_label_len))
  (aliasKey_label_len: UInt32.t)
  (aliasKey_label: B.lbuffer byte_sec (v aliasKey_label_len))
(* DeviceID CSR Inputs*)
  (deviceIDCSR_ingredients:deviceIDCSR_ingredients_t)
(* AliasKey Crt Inputs*)
  (aliasKeyCRT_ingredients:aliasKeyCRT_ingredients_t)
(* Common Outputs *)
  (aliasKey_pub: B.lbuffer byte_pub 32)
  (aliasKey_priv: B.lbuffer uint8 32)
(* DeviceID CSR Outputs *)
  (deviceIDCSR_len: UInt32.t)
  (deviceIDCSR_buf: B.lbuffer byte_pub (v deviceIDCSR_len))
(* AliasKey Crt Outputs *)
  (aliasKeyCRT_len: UInt32.t)
  (aliasKeyCRT_buf: B.lbuffer byte_pub (v aliasKeyCRT_len))
: HST.Stack unit
  (requires fun h ->
                  riot_pre
                        (h) (cdi) (fwid)
                        (deviceID_label_len) (deviceID_label)
                        (aliasKey_label_len) (aliasKey_label)
                        (deviceIDCSR_ingredients)
                        (aliasKeyCRT_ingredients)
                        (aliasKey_pub) (aliasKey_priv)
                        (deviceIDCSR_len) (deviceIDCSR_buf)
                        (aliasKeyCRT_len) (aliasKeyCRT_buf)
   )
   (ensures fun h0 _ h1 ->
                        riot_post
                        (cdi) (fwid)
                        (deviceID_label_len) (deviceID_label)
                        (aliasKey_label_len) (aliasKey_label)
                        (deviceIDCSR_ingredients)
                        (aliasKeyCRT_ingredients)
                        (aliasKey_pub) (aliasKey_priv)
                        (deviceIDCSR_len) (deviceIDCSR_buf)
                        (aliasKeyCRT_len) (aliasKeyCRT_buf)
                        (h0) (h1)
  )
= (**) let h0 = HST.get () in
  HST.push_frame ();
  (**) let hs0 = HST.get () in
  (**) B.fresh_frame_modifies h0 hs0;

(* Derive DeviceID *)
  let deviceID_pub : B.lbuffer byte_pub 32 = B.alloca 0x00uy    32ul in
  let hs1 = HST.get () in
  let deviceID_priv: B.lbuffer byte_sec 32 = B.alloca (u8 0x00) 32ul in
  let hs2 = HST.get () in
  let authKeyID: B.lbuffer byte_pub 20 = B.alloca 0x00uy 20ul in
  let hs3 = HST.get () in

  let _h_step1_pre = HST.get () in
  (**) B.modifies_buffer_elim cdi  B.loc_none h0 hs3;
  (**) B.modifies_buffer_elim fwid B.loc_none h0 hs3;
  (**) B.modifies_buffer_elim deviceID_label B.loc_none h0 hs3;
  (**) B.modifies_buffer_elim deviceID_label B.loc_none h0 hs3;
  riot_core_step1
    (cdi) (fwid)
    (deviceID_label_len) (deviceID_label)
    (aliasKey_label_len) (aliasKey_label)
    (deviceID_pub) (deviceID_priv)
    (aliasKey_pub) (aliasKey_priv)
    (authKeyID);
  let _h_step1_post = HST.get () in
  (**) let hs4 = HST.get () in

  assert (aliasKey_post cdi fwid aliasKey_label_len aliasKey_label aliasKey_pub aliasKey_priv h0 _h_step1_post);

  (**) B.modifies_trans B.loc_none h0 hs3 (
    B.loc_buffer deviceID_pub  `B.loc_union`
    B.loc_buffer deviceID_priv `B.loc_union`
    B.loc_buffer aliasKey_pub  `B.loc_union`
    B.loc_buffer aliasKey_priv `B.loc_union`
    B.loc_buffer authKeyID
  ) hs4;

  let _h_step2_pre = _h_step1_post in

  riot_core_step2
    (* version   *) deviceIDCSR_ingredients.deviceIDCSR_version
                    deviceIDCSR_ingredients.deviceIDCSR_s_common
                    deviceIDCSR_ingredients.deviceIDCSR_s_org
                    deviceIDCSR_ingredients.deviceIDCSR_s_country
    (* key usage *) deviceIDCSR_ingredients.deviceIDCSR_ku
    (* DeviceID  *) deviceID_pub
                    deviceID_priv
    (*DeviceIDCRI*) deviceIDCSR_len
                    deviceIDCSR_buf;
  let _h_step2_post = HST.get () in

  (**) B.modifies_trans (
    B.loc_buffer deviceID_pub  `B.loc_union`
    B.loc_buffer deviceID_priv `B.loc_union`
    B.loc_buffer aliasKey_pub  `B.loc_union`
    B.loc_buffer aliasKey_priv `B.loc_union`
    B.loc_buffer authKeyID
  ) h0 _h_step2_pre (
    B.loc_buffer deviceIDCSR_buf
  ) _h_step2_post;

  assert (
    deviceIDCSR_post
      (cdi) (deviceID_label_len) (deviceID_label)
      (deviceIDCSR_ingredients)
      (deviceIDCSR_len) (deviceIDCSR_buf)
      (h0) (_h_step2_post)
  );

  let _h_step3_pre = _h_step2_post in

  (**) B.modifies_buffer_elim fwid (
         B.loc_buffer deviceID_pub  `B.loc_union`
         B.loc_buffer deviceID_priv `B.loc_union`
         B.loc_buffer aliasKey_pub  `B.loc_union`
         B.loc_buffer aliasKey_priv `B.loc_union`
         B.loc_buffer authKeyID     `B.loc_union`
         B.loc_buffer deviceIDCSR_buf
  ) h0 _h_step3_pre;
  (**) B.modifies_buffer_elim authKeyID     (B.loc_buffer deviceIDCSR_buf) _h_step1_post _h_step3_pre;
  (**) B.modifies_buffer_elim deviceID_pub  (B.loc_buffer deviceIDCSR_buf) _h_step1_post _h_step3_pre;
  (**) B.modifies_buffer_elim deviceID_priv (B.loc_buffer deviceIDCSR_buf) _h_step1_post _h_step3_pre;
  (**) B.modifies_buffer_elim aliasKey_pub  (B.loc_buffer deviceIDCSR_buf) _h_step1_post _h_step3_pre;

  riot_core_step3
    (aliasKeyCRT_ingredients.aliasKeyCrt_version)
    (aliasKeyCRT_ingredients.aliasKeyCrt_serialNumber)
    (aliasKeyCRT_ingredients.aliasKeyCrt_i_common)
    (aliasKeyCRT_ingredients.aliasKeyCrt_i_org)
    (aliasKeyCRT_ingredients.aliasKeyCrt_i_country)
    (aliasKeyCRT_ingredients.aliasKeyCrt_notBefore)
    (aliasKeyCRT_ingredients.aliasKeyCrt_notAfter)
    (aliasKeyCRT_ingredients.aliasKeyCrt_s_common)
    (aliasKeyCRT_ingredients.aliasKeyCrt_s_org)
    (aliasKeyCRT_ingredients.aliasKeyCrt_s_country)
    (fwid)
    (aliasKeyCRT_ingredients.aliasKeyCrt_ku)
    (authKeyID)
    (aliasKeyCRT_ingredients.aliasKeyCrt_riot_version)
    (* DeviceID  *) deviceID_pub
                    deviceID_priv
    (* AliasKey  *) aliasKey_pub
    (*AliasKeyTBS*) aliasKeyCRT_len
                    aliasKeyCRT_buf;
  let _h_step3_post = HST.get () in

  (**) B.modifies_trans (
    B.loc_buffer deviceID_pub  `B.loc_union`
    B.loc_buffer deviceID_priv `B.loc_union`
    B.loc_buffer aliasKey_pub  `B.loc_union`
    B.loc_buffer aliasKey_priv `B.loc_union`
    B.loc_buffer authKeyID     `B.loc_union`
    B.loc_buffer deviceIDCSR_buf
  ) h0 _h_step3_pre (
    B.loc_buffer aliasKeyCRT_buf
  ) _h_step3_post;

  (**) B.modifies_buffer_elim aliasKey_pub (
         B.loc_buffer deviceIDCSR_buf `B.loc_union`
         B.loc_buffer aliasKeyCRT_buf
  ) _h_step1_post _h_step3_post;
  assert (
    aliasKeyCRT_post
      (cdi) (fwid) (deviceID_label_len) (deviceID_label)
      (aliasKeyCRT_ingredients)
      (aliasKeyCRT_len) (aliasKeyCRT_buf)
      (aliasKey_pub)
      (h0) (_h_step3_post)
  );

(* hsf *) let hsf = HST.get () in
  HST.pop_frame ();
(* hf *) let hf = HST.get () in
  (**) B.popped_modifies hsf hf;
  (**) B.modifies_buffer_elim aliasKey_pub    (B.loc_region_only false (HS.get_tip hsf)) hsf hf;
  (**) B.modifies_buffer_elim aliasKey_priv   (B.loc_region_only false (HS.get_tip hsf)) hsf hf;
  (**) B.modifies_buffer_elim deviceIDCSR_buf (B.loc_region_only false (HS.get_tip hsf)) hsf hf;
  (**) B.modifies_buffer_elim aliasKeyCRT_buf (B.loc_region_only false (HS.get_tip hsf)) hsf hf;
  (**) B.modifies_fresh_frame_popped h0 hs0 (
    B.loc_buffer aliasKey_pub    `B.loc_union`
    B.loc_buffer aliasKey_priv   `B.loc_union`
    B.loc_buffer deviceIDCSR_buf `B.loc_union`
    B.loc_buffer aliasKeyCRT_buf
  ) hsf hf;

  assert (HST.equal_domains h0 hf);

  assert (aliasKey_post cdi fwid aliasKey_label_len aliasKey_label aliasKey_pub aliasKey_priv h0 hf);

  assert (
    deviceIDCSR_post
      (cdi) (deviceID_label_len) (deviceID_label)
      (deviceIDCSR_ingredients)
      (deviceIDCSR_len) (deviceIDCSR_buf)
      (h0) (hf)
  );

  assert (
    aliasKeyCRT_post
      (cdi) (fwid) (deviceID_label_len) (deviceID_label)
      (aliasKeyCRT_ingredients)
      (aliasKeyCRT_len) (aliasKeyCRT_buf)
      (aliasKey_pub)
      (h0) (hf)
  )
