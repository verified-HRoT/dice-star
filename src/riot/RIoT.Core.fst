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

let deviceIDCRI_pre (x:deviceIDCSR_ingredients_t) =
  True
  // valid_deviceIDCRI_ingredients
  //   x.deviceIDCSR_version x.deviceIDCSR_s_common x.deviceIDCSR_s_org x.deviceIDCSR_s_country x.deviceIDCSR_ku

[@@ "opaque_to_smt"]
unfold noextract
let coerce_asn1_tlv_int32_of_type_to_asn1_int32 (x:asn1_TLV_int32_of_type SEQUENCE)
  : asn1_int32 = x

let deviceIDCSR_pre (x:deviceIDCSR_ingredients_t{deviceIDCRI_pre x}) (deviceIDCSR_len:UInt32.t) =
  let l = coerce_asn1_tlv_int32_of_type_to_asn1_int32
    (len_of_deviceIDCRI
      x.deviceIDCSR_version x.deviceIDCSR_s_common x.deviceIDCSR_s_org
      x.deviceIDCSR_s_country) in

  valid_deviceIDCSR_ingredients l /\
  eq2 #nat (v deviceIDCSR_len) (length_of_deviceIDCSR l)

let aliasKeyCRT_pre (x:aliasKeyCRT_ingredients_t) (aliasKeyCRT_len:UInt32.t) =
  let l = coerce_asn1_tlv_int32_of_type_to_asn1_int32
    (len_of_aliasKeyTBS
      x.aliasKeyCrt_serialNumber x.aliasKeyCrt_i_common x.aliasKeyCrt_i_org x.aliasKeyCrt_i_country
      x.aliasKeyCrt_s_common x.aliasKeyCrt_s_org x.aliasKeyCrt_s_country
      x.aliasKeyCrt_riot_version) in
  valid_aliasKeyCRT_ingredients l /\
  eq2 #nat (v aliasKeyCRT_len) (length_of_aliasKeyCRT l)

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
     assume (Seq.length aliasKeyTBS_seq == v aliasKeyTBS_len); //TODO: help Z3 prove it
     let aliasKeyCRT: aliasKeyCRT_t aliasKeyTBS_len = sign_and_finalize_aliasKeyCRT_spec
                                                                (deviceID_priv_seq)
                                                                (aliasKeyTBS_len)
                                                                (aliasKeyTBS_seq) in
     B.as_seq h1 aliasKeyCRT_buf == serialize_aliasKeyCRT aliasKeyTBS_len `serialize` aliasKeyCRT


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
  = B.(modifies (loc_buffer deviceIDCSR_buf `loc_union`
                 loc_buffer aliasKeyCRT_buf `loc_union`
                 loc_buffer aliasKey_pub    `loc_union`
                 loc_buffer aliasKey_priv ) h0 h1) /\

    aliasKey_post cdi fwid aliasKey_label_len aliasKey_label aliasKey_pub aliasKey_priv h0 h1 /\
    
    deviceIDCSR_post cdi deviceID_label_len deviceID_label
      deviceIDCSR_ingredients deviceIDCSR_len deviceIDCSR_buf h0 h1 /\
    
    aliasKeyCRT_post cdi fwid deviceID_label_len deviceID_label
      aliasKeyCRT_ingredients aliasKeyCRT_len aliasKeyCRT_buf aliasKey_pub h0 h1

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
  (requires fun h -> riot_pre
                        (h)
                        (cdi)
                        (fwid)
                        (deviceID_label_len) (deviceID_label)
                        (aliasKey_label_len) (aliasKey_label)
                        (deviceIDCSR_ingredients)
                        (aliasKeyCRT_ingredients)
                        (aliasKey_pub) (aliasKey_priv)
                        (deviceIDCSR_len) (deviceIDCSR_buf)
                        (aliasKeyCRT_len) (aliasKeyCRT_buf)
   )
   (ensures fun h0 _ h1 -> riot_post
                        (cdi)
                        (fwid)
                        (deviceID_label_len) (deviceID_label)
                        (aliasKey_label_len) (aliasKey_label)
                        (deviceIDCSR_ingredients)
                        (aliasKeyCRT_ingredients)
                        (aliasKey_pub) (aliasKey_priv)
                        (deviceIDCSR_len) (deviceIDCSR_buf)
                        (aliasKeyCRT_len) (aliasKeyCRT_buf)
                        (h0) (h1))
= HST.push_frame ();

(* Derive DeviceID *)
  let deviceID_pub : B.lbuffer byte_pub 32 = B.alloca 0x00uy    32ul in
  let deviceID_priv: B.lbuffer byte_sec 32 = B.alloca (u8 0x00) 32ul in
  printf "Deriving DeviceID\n" done;
  derive_DeviceID
    (* pub *) deviceID_pub
    (* priv*) deviceID_priv
    (* cdi *) cdi
    (* lbl *) deviceID_label_len
              deviceID_label;

(* A workaround to derive authKeyID for now *)
  let deviceID_pub_sec: B.lbuffer byte_sec 32 = B.alloca (u8 0x00) 32ul in
  let aliasKeyCrt_keyID: B.lbuffer byte_pub 20 = B.alloca 0x00uy 20ul in
  classify_public_buffer 32ul deviceID_pub deviceID_pub_sec;
  derive_authKeyID aliasKeyCrt_keyID deviceID_pub_sec;
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

(* Create DeviceIDCRI *)
   let deviceIDCRI_len: asn1_TLV_int32_of_type SEQUENCE = len_of_deviceIDCRI
                                                            deviceIDCSR_ingredients.deviceIDCSR_version
                                                            deviceIDCSR_ingredients.deviceIDCSR_s_common
                                                            deviceIDCSR_ingredients.deviceIDCSR_s_org
                                                            deviceIDCSR_ingredients.deviceIDCSR_s_country in
   let deviceIDCRI_buf: B.lbuffer byte_pub (v deviceIDCRI_len) = B.alloca 0x00uy deviceIDCRI_len in

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

(* Sign AliasKeyTBS and Finalize AliasKeyCRT *)
  printf "Signing and finalizing AliasKey Certificate\n" done;
  sign_and_finalize_aliasKeyCRT
    (*Signing Key*) deviceID_priv
    (*AliasKeyTBS*) aliasKeyTBS_len
                    aliasKeyTBS_buf
    (*AliasKeyCRT*) aliasKeyCRT_len
                    aliasKeyCRT_buf;

  HST.pop_frame()
