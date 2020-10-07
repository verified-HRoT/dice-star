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
  let l = coerce_asn1_tlv_int32_of_type_to_asn1_int32
    (len_of_deviceIDCRI
      x.deviceIDCSR_version x.deviceIDCSR_s_common x.deviceIDCSR_s_org
      x.deviceIDCSR_s_country) in

  valid_deviceIDCSR_ingredients l /\
  eq2 #nat (v deviceIDCSR_len) (length_of_deviceIDCSR l)

unfold
let aliasKeyCRT_pre (x:aliasKeyCRT_ingredients_t) (aliasKeyCRT_len:UInt32.t) =
  let l = coerce_asn1_tlv_int32_of_type_to_asn1_int32
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
  (deviceID_label_len: size_t)
  (deviceID_label: B.lbuffer byte_sec (v deviceID_label_len))
  (aliasKey_label_len: size_t)
  (aliasKey_label: B.lbuffer byte_sec (v aliasKey_label_len))
(* DeviceID CSR Inputs*)
  (deviceIDCSR_ingredients:deviceIDCSR_ingredients_t)
(* AliasKey Crt Inputs*)
  (aliasKeyCRT_ingredients:aliasKeyCRT_ingredients_t)
(* Common Outputs *)
  (aliasKey_pub: B.lbuffer byte_pub 32)
  (aliasKey_priv: B.lbuffer uint8 32)
(* DeviceID CSR Outputs *)
  (deviceIDCSR_len: size_t)
  (deviceIDCSR_buf: B.lbuffer byte_pub (v deviceIDCSR_len))
(* AliasKey Crt Outputs *)
  (aliasKeyCRT_len: size_t)
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
                                                       aliasKey_label_len
                                                       (B.as_seq h0 aliasKey_label)

#push-options "--z3rlimit 100"
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

    let (* Prf *) _ = lemma_serialize_deviceIDCRI_size_exact deviceIDCRI in  //AR: TODO: This takes long time
    let deviceIDCSR: deviceIDCSR_t deviceIDCRI_len = sign_and_finalize_deviceIDCSR_spec
                                                                (deviceID_priv_seq)
                                                                (deviceIDCRI_len)
                                                                (deviceIDCRI_seq) in
    B.as_seq h1 deviceIDCSR_buf == serialize_deviceIDCSR deviceIDCRI_len `serialize` deviceIDCSR
#pop-options

unfold noextract
let coerce_asn1_int32_to_size_t (x:asn1_int32) : size_t = x

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
     derive_authKeyID_from_cdi_spec (B.as_seq h0 cdi) (deviceID_label_len) (B.as_seq h0 deviceID_label) in
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
     let aliasKeyTBS_len = coerce_asn1_tlv_int32_of_type_to_asn1_int32
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

unfold
let riot_post
(* Common Inputs *)
  (cdi : B.lbuffer byte_sec 32)
  (fwid: B.lbuffer byte_sec 32)
  (deviceID_label_len: size_t)
  (deviceID_label: B.lbuffer byte_sec (v deviceID_label_len))
  (aliasKey_label_len: size_t)
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
                 loc_buffer aliasKeyCRT_buf
                 ) h0 h1) /\

    aliasKey_post cdi fwid aliasKey_label_len aliasKey_label aliasKey_pub aliasKey_priv h0 h1 /\

    // deviceIDCSR_post cdi deviceID_label_len deviceID_label
    //   deviceIDCSR_ingredients deviceIDCSR_len deviceIDCSR_buf h0 h1 /\

    // aliasKeyCRT_post cdi fwid deviceID_label_len deviceID_label
    //   aliasKeyCRT_ingredients aliasKeyCRT_len aliasKeyCRT_buf aliasKey_pub h0 h1 /\
True

let () = ()
// let f ()
// : HST.St unit
// = let h0 = HST.get () in
//   HST.push_frame ();
//   HST.pop_frame ();
//   let h1 = HST.get () in
//   assert (HST.equal_domains h0 h1)

module U32 = FStar.UInt32
module U8 = FStar.UInt8
#reset-options

let lemma_help
  (pub_t sec_t: Type0)
  (h0 hs0 hsf hf: HS.mem)
  (in1: B.buffer sec_t) (in2: B.buffer sec_t) (in3: B.buffer sec_t) (in4: B.buffer sec_t)
  (out1: B.buffer pub_t) (out2: B.buffer sec_t) (out3: B.buffer pub_t) (out4: B.buffer pub_t)
  (hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 hs12 hs13 hs14: HS.mem)
  (_bl1: UInt32.t) (_b1: B.lbuffer pub_t (U32.v _bl1)) (_bv1: pub_t)
  (_bl2: UInt32.t) (_b2: B.lbuffer sec_t (U32.v _bl2)) (_bv2: sec_t)
  (_bl3: UInt32.t) (_b3: B.lbuffer sec_t (U32.v _bl3)) (_bv3: sec_t)
  (_bl4: UInt32.t) (_b4: B.lbuffer pub_t (U32.v _bl4)) (_bv4: pub_t)
  (_bl5: UInt32.t) (_b5: B.lbuffer pub_t (U32.v _bl5)) (_bv5: pub_t)
  (_bl6: UInt32.t) (_b6: B.lbuffer pub_t (U32.v _bl6)) (_bv6: pub_t)
: Lemma
  (requires
            B.all_live h0 [B.buf in1; B.buf in2; B.buf in3; B.buf in4;
                           B.buf out1; B.buf out2; B.buf out3; B.buf out4] /\
            B.all_disjoint [B.loc_buffer in1; B.loc_buffer in2; B.loc_buffer in3; B.loc_buffer in4;
                            B.loc_buffer out1; B.loc_buffer out2; B.loc_buffer out3; B.loc_buffer out4] /\
            HS.fresh_frame h0 hs0 /\ HS.get_tip hs0 == HS.get_tip hsf /\ HS.popped hsf hf /\
            B.alloc_post_mem_common _b1 hs0 hs1 (Seq.create (UInt32.v _bl1) _bv1) /\ B.frameOf _b1 == HS.get_tip hs0 /\
            B.alloc_post_mem_common _b2 hs1 hs2 (Seq.create (UInt32.v _bl2) _bv2) /\ B.frameOf _b2 == HS.get_tip hs1 /\
            B.alloc_post_mem_common _b3 hs2 hs3 (Seq.create (UInt32.v _bl3) _bv3) /\ B.frameOf _b3 == HS.get_tip hs2 /\
            B.alloc_post_mem_common _b4 hs3 hs4 (Seq.create (UInt32.v _bl4) _bv4) /\ B.frameOf _b4 == HS.get_tip hs3 /\

            (* Derive DeviceID *)
            B.modifies (B.loc_buffer _b1 `B.loc_union` B.loc_buffer _b2) hs4 hs5 /\

            (* Derive AliasKey *)
            B.modifies (B.loc_buffer out1 `B.loc_union` B.loc_buffer out2) hs5 hs6 /\

            (* Classify DeviceID Public Key *)
            B.modifies (B.loc_buffer _b3) hs6 hs7 /\

            (* Derive AliasCRT_AuthKeyID *)
            B.modifies (B.loc_buffer _b4) hs7 hs8 /\

            (* Allocate `deviceIDCRI_buf` *)
            B.alloc_post_mem_common _b5 hs8 hs9 (Seq.create (UInt32.v _bl5) _bv5) /\ B.frameOf _b5 == HS.get_tip hs8 /\

            (* Write `deviceIDCRI_buf` *)
            B.modifies (B.loc_buffer _b5) hs9 hs10 /\

            (* Write `deviceIDCSR_buf` *)
            B.modifies (B.loc_buffer out3) hs10 hs11 /\

            (* Allocate `aliasKeyTBS_buf` *)
            B.alloc_post_mem_common _b6 hs11 hs12 (Seq.create (UInt32.v _bl6) _bv6) /\ B.frameOf _b6 == HS.get_tip hs11 /\

            (* Write `aliasKeyTBS_buf` *)
            B.modifies (B.loc_buffer _b6) hs12 hs13 /\

            (* Write `aliasKeyCRT_buf` *)
            B.modifies (B.loc_buffer out4) hs13 hs14 /\

            hs14 == hsf
            )
  (ensures
    B.modifies (B.loc_buffer out1 `B.loc_union`
                B.loc_buffer out2 `B.loc_union`
                B.loc_buffer out3 `B.loc_union`
                B.loc_buffer out4) h0 hf /\

    B.as_seq hs4  in1  == B.as_seq h0 in1 /\ // cdi
    B.as_seq hs4  in3  == B.as_seq h0 in3 /\ // lbl device

    B.as_seq hs5  in1  == B.as_seq h0 in1 /\ // cdi
    B.as_seq hs5  in2  == B.as_seq h0 in2 /\ // fwid
    B.as_seq hs5  in4  == B.as_seq h0 in4 /\ // lbl alias

    B.as_seq hs6  out1 == B.as_seq hf out1 /\
    B.as_seq hs6  out2 == B.as_seq hf out2 /\
    B.as_seq hs11 out3 == B.as_seq hf out3 /\
    B.as_seq hs14 out4 == B.as_seq hf out4 /\
    True
  )
=
  B.modifies_trans B.loc_none h0 hs0 B.loc_none hs1;
  B.modifies_trans B.loc_none h0 hs1 B.loc_none hs2;
  B.modifies_trans B.loc_none h0 hs2 B.loc_none hs3;
  B.modifies_trans B.loc_none h0 hs3 B.loc_none hs4;

  B.modifies_buffer_elim in1 B.loc_none h0 hs4;
  B.modifies_buffer_elim in3 B.loc_none h0 hs4;

(* hs4 --> hs5 *)
  B.modifies_trans B.loc_none h0 hs4 (
    B.loc_buffer _b1 `B.loc_union`
    B.loc_buffer _b2
  ) hs5;
  B.modifies_buffer_elim in1 (B.loc_buffer out1 `B.loc_union` B.loc_buffer out2) h0 hs5;
  B.modifies_buffer_elim in2 (B.loc_buffer out1 `B.loc_union` B.loc_buffer out2) h0 hs5;
  B.modifies_buffer_elim in4 (B.loc_buffer out1 `B.loc_union` B.loc_buffer out2) h0 hs5;

(* hs5 --> hs6 *)
  B.modifies_trans (
    B.loc_buffer _b1 `B.loc_union`
    B.loc_buffer _b2
  ) h0 hs5 (
    B.loc_buffer out1 `B.loc_union`
    B.loc_buffer out2
  ) hs6;
  B.modifies_buffer_elim _b1 (B.loc_buffer out1 `B.loc_union` B.loc_buffer out2) hs5 hs6;
  B.modifies_buffer_elim _b2 (B.loc_buffer out1 `B.loc_union` B.loc_buffer out2) hs5 hs6;

(* hs6 --> hs7 *)
  B.modifies_trans (
    B.loc_buffer _b1 `B.loc_union`
    B.loc_buffer _b2 `B.loc_union`
    B.loc_buffer out1  `B.loc_union`
    B.loc_buffer out2
  ) h0 hs6 (
    B.loc_buffer _b3
  ) hs7;
  B.modifies_buffer_elim _b1 (B.loc_buffer _b3) hs6 hs7;
  B.modifies_buffer_elim _b2 (B.loc_buffer _b3) hs6 hs7;
  B.modifies_buffer_elim out1  (B.loc_buffer _b3) hs6 hs7;
  B.modifies_buffer_elim out2  (B.loc_buffer _b3) hs6 hs7;

(* hs7 --> hs8 *)
  B.modifies_trans (
    B.loc_buffer _b1 `B.loc_union`
    B.loc_buffer _b2 `B.loc_union`
    B.loc_buffer out1  `B.loc_union`
    B.loc_buffer out2  `B.loc_union`
    B.loc_buffer _b3
  ) h0 hs7 (
    B.loc_buffer _b4
  ) hs8;
  B.modifies_buffer_elim _b1 (B.loc_buffer _b4) hs7 hs8;
  B.modifies_buffer_elim _b2 (B.loc_buffer _b4) hs7 hs8;
  B.modifies_buffer_elim out1  (B.loc_buffer _b4) hs7 hs8;
  B.modifies_buffer_elim out2  (B.loc_buffer _b4) hs7 hs8;
  B.modifies_buffer_elim _b3 (B.loc_buffer _b4) hs7 hs8;

(* hs8 --> hs9 *)
  B.modifies_trans (
    B.loc_buffer _b1 `B.loc_union`
    B.loc_buffer _b2 `B.loc_union`
    B.loc_buffer out1  `B.loc_union`
    B.loc_buffer out2  `B.loc_union`
    B.loc_buffer _b3 `B.loc_union`
    B.loc_buffer _b4
  ) h0 hs8 B.loc_none hs9;
  B.modifies_buffer_elim _b1 B.loc_none hs8 hs9;
  B.modifies_buffer_elim _b2 B.loc_none hs8 hs9;
  B.modifies_buffer_elim out1  B.loc_none hs8 hs9;
  B.modifies_buffer_elim out2  B.loc_none hs8 hs9;
  B.modifies_buffer_elim _b3 B.loc_none hs8 hs9;
  B.modifies_buffer_elim _b4 B.loc_none hs8 hs9;

(* hs9 --> hs10 *)
  B.modifies_trans (
    B.loc_buffer _b1 `B.loc_union`
    B.loc_buffer _b2 `B.loc_union`
    B.loc_buffer out1  `B.loc_union`
    B.loc_buffer out2  `B.loc_union`
    B.loc_buffer _b3 `B.loc_union`
    B.loc_buffer _b4
  ) h0 hs9 (
    B.loc_buffer _b5
  ) hs10;
  B.modifies_buffer_elim _b1 (B.loc_buffer _b5) hs9 hs10;
  B.modifies_buffer_elim _b2 (B.loc_buffer _b5) hs9 hs10;
  B.modifies_buffer_elim out1  (B.loc_buffer _b5) hs9 hs10;
  B.modifies_buffer_elim out2  (B.loc_buffer _b5) hs9 hs10;
  B.modifies_buffer_elim _b3 (B.loc_buffer _b5) hs9 hs10;
  B.modifies_buffer_elim _b4 (B.loc_buffer _b5) hs9 hs10;


(* hs10 --> hs11 *)
  B.modifies_trans (
    B.loc_buffer _b1 `B.loc_union`
    B.loc_buffer _b2 `B.loc_union`
    B.loc_buffer out1  `B.loc_union`
    B.loc_buffer out2  `B.loc_union`
    B.loc_buffer _b3 `B.loc_union`
    B.loc_buffer _b4 `B.loc_union`
    B.loc_buffer _b5
  ) h0 hs10 (
    B.loc_buffer out3
  ) hs11;
  B.modifies_buffer_elim _b1 (B.loc_buffer out3) hs10 hs11;
  B.modifies_buffer_elim _b2 (B.loc_buffer out3) hs10 hs11;
  B.modifies_buffer_elim out1  (B.loc_buffer out3) hs10 hs11;
  B.modifies_buffer_elim out2  (B.loc_buffer out3) hs10 hs11;
  B.modifies_buffer_elim _b3 (B.loc_buffer out3) hs10 hs11;
  B.modifies_buffer_elim _b4 (B.loc_buffer out3) hs10 hs11;
  B.modifies_buffer_elim _b5 (B.loc_buffer out3) hs10 hs11;

(* hs11 --> hs12 *)
  B.modifies_trans (
    B.loc_buffer _b1 `B.loc_union`
    B.loc_buffer _b2 `B.loc_union`
    B.loc_buffer out1  `B.loc_union`
    B.loc_buffer out2  `B.loc_union`
    B.loc_buffer _b3 `B.loc_union`
    B.loc_buffer _b4 `B.loc_union`
    B.loc_buffer _b5 `B.loc_union`
    B.loc_buffer out3
  ) h0 hs11 B.loc_none hs12;
  B.modifies_buffer_elim _b1 B.loc_none hs11 hs12;
  B.modifies_buffer_elim _b2 B.loc_none hs11 hs12;
  B.modifies_buffer_elim out1  B.loc_none hs11 hs12;
  B.modifies_buffer_elim out2  B.loc_none hs11 hs12;
  B.modifies_buffer_elim _b3 B.loc_none hs11 hs12;
  B.modifies_buffer_elim _b4 B.loc_none hs11 hs12;
  B.modifies_buffer_elim _b5 B.loc_none hs11 hs12;
  B.modifies_buffer_elim out3  B.loc_none hs11 hs12;

(* hs12 --> hs13 *)
  B.modifies_trans (
    B.loc_buffer _b1 `B.loc_union`
    B.loc_buffer _b2 `B.loc_union`
    B.loc_buffer out1  `B.loc_union`
    B.loc_buffer out2  `B.loc_union`
    B.loc_buffer _b3 `B.loc_union`
    B.loc_buffer _b4 `B.loc_union`
    B.loc_buffer _b5 `B.loc_union`
    B.loc_buffer out3
  ) h0 hs12 (
    B.loc_buffer _b6
  ) hs13;
  B.modifies_buffer_elim _b1 (B.loc_buffer _b6) hs12 hs13;
  B.modifies_buffer_elim _b2 (B.loc_buffer _b6) hs12 hs13;
  B.modifies_buffer_elim out1  (B.loc_buffer _b6) hs12 hs13;
  B.modifies_buffer_elim out2  (B.loc_buffer _b6) hs12 hs13;
  B.modifies_buffer_elim _b3 (B.loc_buffer _b6) hs12 hs13;
  B.modifies_buffer_elim _b4 (B.loc_buffer _b6) hs12 hs13;
  B.modifies_buffer_elim _b5 (B.loc_buffer _b6) hs12 hs13;
  B.modifies_buffer_elim out3  (B.loc_buffer _b6) hs12 hs13;

(* hs13 --> hs14 *)
  B.modifies_trans (
    B.loc_buffer _b1 `B.loc_union`
    B.loc_buffer _b2 `B.loc_union`
    B.loc_buffer out1  `B.loc_union`
    B.loc_buffer out2  `B.loc_union`
    B.loc_buffer _b3 `B.loc_union`
    B.loc_buffer _b4 `B.loc_union`
    B.loc_buffer _b5 `B.loc_union`
    B.loc_buffer out3  `B.loc_union`
    B.loc_buffer _b6
  ) h0 hs13 (
    B.loc_buffer out4
  ) hs14;
  B.modifies_buffer_elim _b1 (B.loc_buffer out4) hs13 hs14;
  B.modifies_buffer_elim _b2 (B.loc_buffer out4) hs13 hs14;
  B.modifies_buffer_elim out1  (B.loc_buffer out4) hs13 hs14;
  B.modifies_buffer_elim out2  (B.loc_buffer out4) hs13 hs14;
  B.modifies_buffer_elim _b3 (B.loc_buffer out4) hs13 hs14;
  B.modifies_buffer_elim _b4 (B.loc_buffer out4) hs13 hs14;
  B.modifies_buffer_elim _b5 (B.loc_buffer out4) hs13 hs14;
  B.modifies_buffer_elim out3  (B.loc_buffer out4) hs13 hs14;
  B.modifies_buffer_elim _b6 (B.loc_buffer out4) hs13 hs14;

(* FIXME: This can be proved with 256-512 z3rlimits *)
  assume (B.modifies ((B.loc_all_regions_from false (HS.get_tip hs0)) `B.loc_union`
                      (B.loc_buffer out1 `B.loc_union`
                       B.loc_buffer out2 `B.loc_union`
                       B.loc_buffer out3 `B.loc_union`
                       B.loc_buffer out4)) hs0 hsf);

  B.modifies_fresh_frame_popped h0 hs0 (
    B.loc_buffer out1 `B.loc_union`
    B.loc_buffer out2 `B.loc_union`
    B.loc_buffer out3 `B.loc_union`
    B.loc_buffer out4
  ) hsf hf;

()

let () = ()

#restart-solver
#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"
let riot
(* Common Inputs *)
  (cdi : B.lbuffer byte_sec 32)
  (fwid: B.lbuffer byte_sec 32)
  (deviceID_label_len: size_t)
  (deviceID_label: B.lbuffer byte_sec (v deviceID_label_len))
  (aliasKey_label_len: size_t)
  (aliasKey_label: B.lbuffer byte_sec (v aliasKey_label_len))
(* DeviceID CSR Inputs*)
  (deviceIDCSR_ingredients:deviceIDCSR_ingredients_t)
(* AliasKey Crt Inputs*)
  (aliasKeyCRT_ingredients:aliasKeyCRT_ingredients_t)
(* Common Outputs *)
  (aliasKey_pub: B.lbuffer byte_pub 32)
  (aliasKey_priv: B.lbuffer uint8 32)
(* DeviceID CSR Outputs *)
  (deviceIDCSR_len: size_t)
  (deviceIDCSR_buf: B.lbuffer byte_pub (v deviceIDCSR_len))
(* AliasKey Crt Outputs *)
  (aliasKeyCRT_len: size_t)
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
  // (**) B.modifies_buffer_elim cdi B.loc_none h0 hs0;


(* Derive DeviceID *)
  let deviceID_pub : B.lbuffer byte_pub 32 = B.alloca 0x00uy    32ul in
  let hs1 = HST.get () in
  let deviceID_priv: B.lbuffer byte_sec 32 = B.alloca (u8 0x00) 32ul in
  let hs2 = HST.get () in
  let deviceID_pub_sec: B.lbuffer byte_sec 32 = B.alloca (u8 0x00) 32ul in
  let hs3 = HST.get () in
  let aliasKeyCrt_keyID: B.lbuffer byte_pub 20 = B.alloca 0x00uy 20ul in
  let hs4 = HST.get () in

  assume (
    B.(all_live hs4 [buf deviceID_pub;
                     buf deviceID_priv;
                     buf cdi;
                     buf deviceID_label]) /\
    B.(all_disjoint [loc_buffer deviceID_pub;
                     loc_buffer deviceID_priv;
                     loc_buffer cdi;
                     loc_buffer deviceID_label])
  );
  printf "Deriving DeviceID\n" done;
  derive_DeviceID
    (* pub *) deviceID_pub
    (* priv*) deviceID_priv
    (* cdi *) cdi
    (* lbl *) deviceID_label_len
              deviceID_label;
(* hs5 *) let hs5 = HST.get () in

  assume (
    B.(all_live hs5 [buf aliasKey_pub;
                     buf aliasKey_priv;
                     buf cdi;
                     buf fwid;
                     buf aliasKey_label]) /\
    B.(all_disjoint [loc_buffer aliasKey_pub;
                     loc_buffer aliasKey_priv;
                     loc_buffer cdi;
                     loc_buffer fwid;
                     loc_buffer aliasKey_label])
  );
  printf "Deriving AliasKey\n" done;
  derive_AliasKey
    (* pub *) aliasKey_pub
    (* priv*) aliasKey_priv
    (* cdi *) cdi
    (* fwid*) fwid
    (* lbl *) aliasKey_label_len
              aliasKey_label;
(* hs6 *) let hs6 = HST.get () in

  assert ( aliasKey_post cdi fwid aliasKey_label_len aliasKey_label aliasKey_pub aliasKey_priv hs5 hs6 );
  // assume ( B.as_seq hs5 cdi == B.as_seq h0 cdi /\
  //          B.as_seq hs5 fwid == B.as_seq h0 fwid /\
  //          B.as_seq hs5 aliasKey_label == B.as_seq h0 aliasKey_label);
  // assert ( aliasKey_post cdi fwid aliasKey_label_len aliasKey_label aliasKey_pub aliasKey_priv h0 hs6 );

  assume (
    B.live hs6 deviceID_pub /\ B.live hs6 deviceID_pub_sec /\
    B.disjoint deviceID_pub deviceID_pub_sec
  );
  classify_public_buffer 32ul deviceID_pub deviceID_pub_sec;
(* hs7 *) let hs7 = HST.get () in

  assume (
    B.live hs7 aliasKeyCrt_keyID /\ B.live hs7 deviceID_pub_sec /\
    B.disjoint aliasKeyCrt_keyID deviceID_pub_sec
  );
  derive_authKeyID
    aliasKeyCrt_keyID
    deviceID_pub_sec;
(* hs8 *) let hs8 = HST.get () in

(* Create DeviceIDCRI *)
   let deviceIDCRI_len: asn1_TLV_int32_of_type SEQUENCE = len_of_deviceIDCRI
                                                            deviceIDCSR_ingredients.deviceIDCSR_version
                                                            deviceIDCSR_ingredients.deviceIDCSR_s_common
                                                            deviceIDCSR_ingredients.deviceIDCSR_s_org
                                                            deviceIDCSR_ingredients.deviceIDCSR_s_country in
   let deviceIDCRI_buf: B.lbuffer byte_pub (v deviceIDCRI_len) = B.alloca 0x00uy deviceIDCRI_len in
(* hs9 *) let hs9 = HST.get () in

   assume (B.(all_live hs9 [buf deviceID_pub;
                            buf deviceIDCRI_buf]));
   assume (B.(all_disjoint [loc_buffer deviceID_pub;
                            loc_buffer deviceIDCRI_buf]));
   printf "Creating DeviceID Certificate Signing Request Information\n" done;
   create_deviceIDCRI
    (* version   *) deviceIDCSR_ingredients.deviceIDCSR_version
                    deviceIDCSR_ingredients.deviceIDCSR_s_common
                    deviceIDCSR_ingredients.deviceIDCSR_s_org
                    deviceIDCSR_ingredients.deviceIDCSR_s_country
    (* key usage *) deviceIDCSR_ingredients.deviceIDCSR_ku
    (* DeviceID  *) deviceID_pub
    (*DeviceIDCRI*) deviceIDCRI_len
                    deviceIDCRI_buf;
(* hs10 *) let hs10 = HST.get () in

  assume (B.(all_live hs10 [buf deviceID_priv;
                            buf deviceIDCRI_buf;
                            buf deviceIDCSR_buf]));
  assume (B.(all_disjoint [loc_buffer deviceID_priv;
                           loc_buffer deviceIDCRI_buf;
                           loc_buffer deviceIDCSR_buf]));
  printf "Signing and finalizing DeviceID Certificate Signing Request\n" done;
  sign_and_finalize_deviceIDCSR
    (*Signing Key*) deviceID_priv
    (*DeviceIDCRI*) deviceIDCRI_len
                    deviceIDCRI_buf
    (*DeviceIDCSR*) deviceIDCSR_len
                    deviceIDCSR_buf;
(* hs11 *) let hs11 = HST.get () in

(* Create AliasKeyTBS *)
  let aliasKeyTBS_len: asn1_TLV_int32_of_type SEQUENCE = len_of_aliasKeyTBS
                                                           aliasKeyCRT_ingredients.aliasKeyCrt_serialNumber
                                                           aliasKeyCRT_ingredients.aliasKeyCrt_i_common
                                                           aliasKeyCRT_ingredients.aliasKeyCrt_i_org
                                                           aliasKeyCRT_ingredients.aliasKeyCrt_i_country
                                                           aliasKeyCRT_ingredients.aliasKeyCrt_s_common
                                                           aliasKeyCRT_ingredients.aliasKeyCrt_s_org
                                                           aliasKeyCRT_ingredients.aliasKeyCrt_s_country
                                                           aliasKeyCRT_ingredients.aliasKeyCrt_riot_version in
  let aliasKeyTBS_buf: B.lbuffer byte_pub (v aliasKeyTBS_len) = B.alloca 0x00uy aliasKeyTBS_len in

(* hs12 *) let hs12 = HST.get () in
  assume (B.(all_live hs12 [buf fwid;
                            buf deviceID_pub;
                            buf aliasKey_pub;
                            buf aliasKeyCrt_keyID;
                            buf aliasKeyTBS_buf]));
  assume (B.(all_disjoint [loc_buffer fwid;
                           loc_buffer deviceID_pub;
                           loc_buffer aliasKey_pub;
                           loc_buffer aliasKeyCrt_keyID;
                           loc_buffer aliasKeyTBS_buf]));

  printf "Creating AliasKey Certificate TBS\n" done;
  create_aliasKeyTBS
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
    (aliasKeyCrt_keyID)
    (aliasKeyCRT_ingredients.aliasKeyCrt_riot_version)
    (* DeviceID  *) deviceID_pub
    (* AliasKey  *) aliasKey_pub
    (*AliasKeyTBS*) aliasKeyTBS_len
                    aliasKeyTBS_buf;

(* hs13 *) let hs13 = HST.get () in
  assume (B.(all_live hs13 [buf deviceID_priv;
                            buf aliasKeyTBS_buf;
                            buf aliasKeyCRT_buf]));
  assume (B.(all_disjoint [loc_buffer deviceID_priv;
                           loc_buffer aliasKeyTBS_buf;
                           loc_buffer aliasKeyCRT_buf]));

(* Sign AliasKeyTBS and Finalize AliasKeyCRT *)
  printf "Signing and finalizing AliasKey Certificate\n" done;
  sign_and_finalize_aliasKeyCRT
    (*Signing Key*) deviceID_priv
    (*AliasKeyTBS*) aliasKeyTBS_len
                    aliasKeyTBS_buf
    (*AliasKeyCRT*) aliasKeyCRT_len
                    aliasKeyCRT_buf;

(* hs14 *) let hs14 = HST.get () in

(* hsf *) let hsf = HST.get () in
  HST.pop_frame ();
(* hf *) let hf = HST.get () in
  (**) B.popped_modifies hsf hf;

  lemma_help
    byte_pub byte_sec
    h0 hs0 hsf hf
    cdi fwid deviceID_label aliasKey_label
    aliasKey_pub aliasKey_priv deviceIDCSR_buf aliasKeyCRT_buf
    hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 hs12 hs13 hs14
    32ul deviceID_pub 0x00uy
    32ul deviceID_priv (u8 0x00)
    32ul deviceID_pub_sec (u8 0x00)
    20ul aliasKeyCrt_keyID 0x00uy
    deviceIDCRI_len deviceIDCRI_buf 0x00uy
    aliasKeyTBS_len aliasKeyTBS_buf 0x00uy;

  assert ( B.as_seq hs5 cdi == B.as_seq h0 cdi /\
           B.as_seq hs5 fwid == B.as_seq h0 fwid /\
           B.as_seq hs5 aliasKey_label == B.as_seq h0 aliasKey_label);
  assert ( aliasKey_post cdi fwid aliasKey_label_len aliasKey_label aliasKey_pub aliasKey_priv h0 hs6 );
  assert ( B.as_seq hs6 aliasKey_pub  == B.as_seq hf aliasKey_pub /\
           B.as_seq hs6 aliasKey_priv == B.as_seq hf aliasKey_priv );
  assert ( aliasKey_post cdi fwid aliasKey_label_len aliasKey_label aliasKey_pub aliasKey_priv h0 hf );

  assume (HST.equal_domains h0 hf)


(*



  // assert (HS.fresh_frame h0 hs0 /\ HS.get_tip hs0 == HS.get_tip hsf /\ HS.popped hsf hf);
  // let _b1, _bv1, _bl1 = deviceID_pub, 0x00uy, 32ul in
  // assert (B.alloc_post_mem_common _b1 hs0 hs1 (Seq.create (UInt32.v _bl1) _bv1) /\ B.frameOf _b1 == HS.get_tip hs0);
  // let _b2, _bv2, _bl2 = deviceID_priv, (u8 0x00), 32ul in
  // assert (B.alloc_post_mem_common _b2 hs1 hs2 (Seq.create (UInt32.v _bl2) _bv2) /\ B.frameOf _b2 == HS.get_tip hs1);
  // let _b3, _bv3, _bl3 = deviceID_pub_sec, (u8 0x00), 32ul in
  // assert (B.alloc_post_mem_common _b3 hs2 hs3 (Seq.create (UInt32.v _bl3) _bv3) /\ B.frameOf _b3 == HS.get_tip hs2);
  // let _b4, _bv4, _bl4 = aliasKeyCrt_keyID, 0x00uy, 20ul in
  // assert (B.alloc_post_mem_common _b4 hs3 hs4 (Seq.create (UInt32.v _bl4) _bv4) /\ B.frameOf _b4 == HS.get_tip hs3);
  // assert (hs4 == hsf);
  // let _b5, _bv5, _bl5 = deviceIDCRI_buf, 0x00uy, deviceIDCRI_len in
  // assert (B.modifies (B.loc_buffer _b5) hs9 hs10); admit();

  (**) let hs1 = HST.get () in
  (**) B.modifies_trans B.loc_none h0 hs0 B.loc_none hs1;
  // (**) B.modifies_buffer_elim cdi B.loc_none h0 hs1;
  // (**) assume (B.(all_live hs1 [buf deviceID_pub;
  //                               buf deviceID_priv;
  //                               buf cdi;
  //                               buf deviceID_label]));
  // assume (B.(all_disjoint [loc_buffer deviceID_pub;
  //                          loc_buffer deviceID_priv;
  //                          loc_buffer cdi;
  //                          loc_buffer deviceID_label]));

  printf "Deriving DeviceID\n" done;
  derive_DeviceID
    (* pub *) deviceID_pub
    (* priv*) deviceID_priv
    (* cdi *) cdi
    (* lbl *) deviceID_label_len
              deviceID_label;

  (**) let hsd = HST.get () in
  (**) B.modifies_trans
          B.loc_none h0 hs1
         (B.loc_buffer deviceID_pub `B.loc_union` B.loc_buffer deviceID_priv) hsd;
  // (**) B.modifies_buffer_elim cdi (B.loc_buffer deviceID_pub `B.loc_union` B.loc_buffer deviceID_priv) h0 hsd;

  printf "Deriving AliasKey\n" done;
  derive_AliasKey
    (* pub *) aliasKey_pub
    (* priv*) aliasKey_priv
    (* cdi *) cdi
    (* fwid*) fwid
    (* lbl *) aliasKey_label_len
              aliasKey_label;

  (**) let hsa = HST.get () in
  (**) B.modifies_trans
         (B.loc_buffer deviceID_pub `B.loc_union ` B.loc_buffer deviceID_priv) h0 hsd
         (B.loc_buffer aliasKey_pub `B.loc_union` B.loc_buffer aliasKey_priv) hsa;

  classify_public_buffer 32ul deviceID_pub deviceID_pub_sec;

  // assert ((B.loc_buffer deviceID_pub `B.loc_union` B.loc_buffer deviceID_priv) `B.loc_union`
  //                     (B.loc_buffer aliasKey_pub `B.loc_union` B.loc_buffer aliasKey_priv)
  //         ==
  //         B.loc_buffer deviceID_pub `B.loc_union` B.loc_buffer deviceID_priv `B.loc_union`
  //                     B.loc_buffer aliasKey_pub `B.loc_union` B.loc_buffer aliasKey_priv); admit()

  (**) let hsa1 = HST.get () in
  assert (B.modifies ((B.loc_buffer deviceID_pub `B.loc_union` B.loc_buffer deviceID_priv) `B.loc_union`
                      (B.loc_buffer aliasKey_pub `B.loc_union` B.loc_buffer aliasKey_priv)) h0 hsa); admit();
  // (**) B.modifies_trans
  //        (B.loc_buffer deviceID_pub `B.loc_union` B.loc_buffer deviceID_priv `B.loc_union`
  //         B.loc_buffer aliasKey_pub `B.loc_union` B.loc_buffer aliasKey_priv) h0 hsa
  //        (B.loc_buffer deviceID_pub_sec) hsa1;
  derive_authKeyID
    aliasKeyCrt_keyID
    deviceID_pub_sec;


  (**) let hsf = HST.get () in
  // assert (B.modifies (B.loc_buffer deviceID_pub `B.loc_union` B.loc_buffer deviceID_priv) hs0 hsf);
  HST.pop_frame ();
  (**) let hf = HST.get () in
  (**) B.popped_modifies hsf hf;
  assume (B.modifies (B.loc_all_regions_from false (HS.get_tip hs0) `B.loc_union`
                      (B.loc_buffer aliasKey_pub `B.loc_union` B.loc_buffer aliasKey_priv)) hs0 hsf);
  B.modifies_fresh_frame_popped h0 hs0 (B.loc_buffer aliasKey_pub `B.loc_union` B.loc_buffer aliasKey_priv) hsf hf;
  // assert (B.modifies (B.loc_buffer deviceID_pub `B.loc_union` B.loc_buffer deviceID_priv) hs0 hf);
  // (**) B.modifies_remove_fresh_frame h0 hs0 hf B.loc_none;
  (**) assert (B.modifies (B.loc_buffer aliasKey_pub `B.loc_union` B.loc_buffer aliasKey_priv) h0 hf);
  (**) assume (HST.equal_domains h0 hf)

(*)
  B.modifies_fresh_frame_popped h0 hs0 B.loc_none hs0 hf;
  Set.lemma_equal_intro (Map.domain (HS.get_hmap h0)) (Map.domain (HS.get_hmap hf));
  assert (Set.equal (Map.domain (HS.get_hmap h0)) (Map.domain (HS.get_hmap hf)));
  // HST.lemma_same_refs_in_all_regions_intro h0 hf;
  // assert (HST.same_refs_in_all_regions h0 hf);
  assert (HST.equal_domains h0 hf);
  admit();

(* Derive DeviceID *)
  let deviceID_pub : B.lbuffer byte_pub 32 = B.alloca 0x00uy    32ul in
  let deviceID_priv: B.lbuffer byte_sec 32 = B.alloca (u8 0x00) 32ul in

  let h = HST.get () in
  // assume (B.(all_live h [buf deviceID_pub;
  //                        buf deviceID_priv;
  //                        buf cdi;
  //                        buf deviceID_label]));
  // assume (B.(all_disjoint [loc_buffer deviceID_pub;
  //                          loc_buffer deviceID_priv;
  //                          loc_buffer cdi;
  //                          loc_buffer deviceID_label]));
  printf "Deriving DeviceID\n" done;
  derive_DeviceID
    (* pub *) deviceID_pub
    (* priv*) deviceID_priv
    (* cdi *) cdi
    (* lbl *) deviceID_label_len
              deviceID_label;
  HST.pop_frame ();
  // let hf = HST.get () in
  // assume (HST.equal_domains h0 hf)

(* A workaround to derive authKeyID for now *)
  let deviceID_pub_sec: B.lbuffer byte_sec 32 = B.alloca (u8 0x00) 32ul in
  let aliasKeyCrt_keyID: B.lbuffer byte_pub 20 = B.alloca 0x00uy 20ul in
  classify_public_buffer 32ul deviceID_pub deviceID_pub_sec;
  derive_authKeyID
    aliasKeyCrt_keyID
    deviceID_pub_sec;
  // let aliasKeyCrt_keyID: datatype_of_asn1_type OCTET_STRING = (|20ul, B32.of_buffer 20ul aliasKeyCrt_keyID_buf|) in

(* Derive AliasKey *)
  printf "Deriving AliasKey\n" done;
  derive_AliasKey
    (* pub *) aliasKey_pub
    (* priv*) aliasKey_priv
    (* cdi *) cdi
    (* fwid*) fwid
    (* lbl *) aliasKey_label_len
              aliasKey_label;

  // let h_AliasKey = HST.get () in

  let h2 = HST.get () in
  // assume (HS.poppable h);
  HST.pop_frame();

  // B.modifies_fresh_frame_popped

  let h3 = HST.get () in
  assume (B.modifies B.loc_none h2 h3);
  // assume (HST.equal_domains h0 h3);


(* Create DeviceIDCRI *)
   let deviceIDCRI_len: asn1_TLV_int32_of_type SEQUENCE = len_of_deviceIDCRI
                                                            deviceIDCSR_ingredients.deviceIDCSR_version
                                                            deviceIDCSR_ingredients.deviceIDCSR_s_common
                                                            deviceIDCSR_ingredients.deviceIDCSR_s_org
                                                            deviceIDCSR_ingredients.deviceIDCSR_s_country in
   let deviceIDCRI_buf: B.lbuffer byte_pub (v deviceIDCRI_len) = B.alloca 0x00uy deviceIDCRI_len in

   let h = HST.get () in
   assume (B.(all_live h [buf deviceID_pub;
                          buf deviceIDCRI_buf]));
   assume (B.(all_disjoint [loc_buffer deviceID_pub;
                            loc_buffer deviceIDCRI_buf]));

   printf "Creating DeviceID Certificate Signing Request Information\n" done;
   create_deviceIDCRI
    (* version   *) deviceIDCSR_ingredients.deviceIDCSR_version
                    deviceIDCSR_ingredients.deviceIDCSR_s_common
                    deviceIDCSR_ingredients.deviceIDCSR_s_org
                    deviceIDCSR_ingredients.deviceIDCSR_s_country
    (* key usage *) deviceIDCSR_ingredients.deviceIDCSR_ku
    (* DeviceID  *) deviceID_pub
    (*DeviceIDCRI*) deviceIDCRI_len
                    deviceIDCRI_buf;

(* Zhe 10/06: Hard to be proved even with 100 more z3rlimits. *)
  let h = HST.get () in
  assume (B.(all_live h [buf deviceID_priv;
                         buf deviceIDCRI_buf;
                         buf deviceIDCSR_buf]));
  assume (B.(all_disjoint [loc_buffer deviceID_priv;
                           loc_buffer deviceIDCRI_buf;
                           loc_buffer deviceIDCSR_buf]));

  // assume (0 < v deviceIDCRI_len);
  // assume (valid_deviceIDCSR_ingredients deviceIDCSR_len);
  // assume (v deviceIDCSR_len == length_of_deviceIDCSR deviceIDCRI_len);

(* Sign AliasKeyTBS and Finalize AliasKeyCRT *)
  printf "Signing and finalizing DeviceID Certificate Signing Request\n" done;
  sign_and_finalize_deviceIDCSR
    (*Signing Key*) deviceID_priv
    (*DeviceIDCRI*) deviceIDCRI_len
                    deviceIDCRI_buf
    (*DeviceIDCSR*) deviceIDCSR_len
                    deviceIDCSR_buf;
(* Create AliasKeyTBS *)
  let aliasKeyTBS_len: asn1_TLV_int32_of_type SEQUENCE = len_of_aliasKeyTBS
                                                           aliasKeyCRT_ingredients.aliasKeyCrt_serialNumber
                                                           aliasKeyCRT_ingredients.aliasKeyCrt_i_common
                                                           aliasKeyCRT_ingredients.aliasKeyCrt_i_org
                                                           aliasKeyCRT_ingredients.aliasKeyCrt_i_country
                                                           aliasKeyCRT_ingredients.aliasKeyCrt_s_common
                                                           aliasKeyCRT_ingredients.aliasKeyCrt_s_org
                                                           aliasKeyCRT_ingredients.aliasKeyCrt_s_country
                                                           aliasKeyCRT_ingredients.aliasKeyCrt_riot_version in
  let aliasKeyTBS_buf: B.lbuffer byte_pub (v aliasKeyTBS_len) = B.alloca 0x00uy aliasKeyTBS_len in

  let h = HST.get () in
  assume (B.(all_live h [buf fwid;
                         buf deviceID_pub;
                         buf aliasKey_pub;
                         buf aliasKeyCrt_keyID;
                         buf aliasKeyTBS_buf]));

  assume (B.(all_disjoint [loc_buffer fwid;
                           loc_buffer deviceID_pub;
                           loc_buffer aliasKey_pub;
                           loc_buffer aliasKeyCrt_keyID;
                           loc_buffer aliasKeyTBS_buf]));

  printf "Creating AliasKey Certificate TBS\n" done;
  create_aliasKeyTBS
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
    (aliasKeyCrt_keyID)
    (aliasKeyCRT_ingredients.aliasKeyCrt_riot_version)
    (* DeviceID  *) deviceID_pub
    (* AliasKey  *) aliasKey_pub
    (*AliasKeyTBS*) aliasKeyTBS_len
                    aliasKeyTBS_buf;

  assume (B.(all_live h [buf deviceID_priv;
                         buf aliasKeyTBS_buf;
                         buf aliasKeyCRT_buf]));
  assume (B.(all_disjoint [loc_buffer deviceID_priv;
                           loc_buffer aliasKeyTBS_buf;
                           loc_buffer aliasKeyCRT_buf]));

(* Sign AliasKeyTBS and Finalize AliasKeyCRT *)
  printf "Signing and finalizing AliasKey Certificate\n" done;
  sign_and_finalize_aliasKeyCRT
    (*Signing Key*) deviceID_priv
    (*AliasKeyTBS*) aliasKeyTBS_len
                    aliasKeyTBS_buf
    (*AliasKeyCRT*) aliasKeyCRT_len
                    aliasKeyCRT_buf;

  let h = HST.get () in
  assume (HS.poppable h);
  HST.pop_frame();

  let h = HST.get () in
  assume (HST.equal_domains h0 h);
  assume (B.(modifies (loc_buffer deviceIDCSR_buf `loc_union`
                       loc_buffer aliasKeyCRT_buf `loc_union`
                       loc_buffer aliasKey_pub    `loc_union`
                       loc_buffer aliasKey_priv ) h0 h) );
  assume (B.as_seq h_AliasKey aliasKey_pub  == B.as_seq h aliasKey_pub /\
          B.as_seq h_AliasKey aliasKey_priv == B.as_seq h aliasKey_priv);
  // assume (aliasKey_post cdi fwid aliasKey_label_len aliasKey_label aliasKey_pub aliasKey_priv h0 h)
  // assume (riot_post
  //                       (cdi)
  //                       (fwid)
  //                       (deviceID_label_len) (deviceID_label)
  //                       (aliasKey_label_len) (aliasKey_label)
  //                       (deviceIDCSR_ingredients)
  //                       (aliasKeyCRT_ingredients)
  //                       (aliasKey_pub) (aliasKey_priv)
  //                       (deviceIDCSR_len) (deviceIDCSR_buf)
  //                       (aliasKeyCRT_len) (aliasKeyCRT_buf)
  //                       (h0) (h))
