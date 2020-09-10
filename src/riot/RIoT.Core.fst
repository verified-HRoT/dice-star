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

#set-options "--z3rlimit 4096 --fuel 0 --ifuel 0"

#restart-solver
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
  (deviceIDCSR_ku: key_usage_payload_t)
  (deviceIDCSR_version: datatype_of_asn1_type INTEGER)
  (deviceIDCSR_s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (deviceIDCSR_s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (deviceIDCSR_s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
(* AliasKey Crt Inputs*)
  (aliasKeyCrt_version: x509_version_t)
  (aliasKeyCrt_serialNumber: x509_serialNumber_t)
  (aliasKeyCrt_i_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (aliasKeyCrt_i_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (aliasKeyCrt_i_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (aliasKeyCrt_notBefore: datatype_of_asn1_type Generalized_Time)
  (aliasKeyCrt_notAfter : datatype_of_asn1_type Generalized_Time)
  (aliasKeyCrt_s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (aliasKeyCrt_s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (aliasKeyCrt_s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (aliasKeyCrt_ku: key_usage_payload_t)
  (riot_version: datatype_of_asn1_type INTEGER)
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
   (* Pre: DeviceIDCRI template has a valid length *)
   valid_deviceIDCRI_ingredients
     deviceIDCSR_version
     deviceIDCSR_s_common deviceIDCSR_s_org deviceIDCSR_s_country
     deviceIDCSR_ku /\
   (* Pre: DeviceIDCSR will have a valid length *)
   valid_deviceIDCSR_ingredients
     (len_of_deviceIDCRI
       deviceIDCSR_version
       deviceIDCSR_s_common deviceIDCSR_s_org deviceIDCSR_s_country
       deviceIDCSR_ku) /\
   (* Pre: `deviceIDCSR_buf` has exact size to write DeviceIDCSR *)
   v deviceIDCSR_len == length_of_deviceIDCSR
                          (len_of_deviceIDCRI
                            deviceIDCSR_version
                            deviceIDCSR_s_common deviceIDCSR_s_org deviceIDCSR_s_country
                            deviceIDCSR_ku) /\
   (* Pre: AliasKeyTBS template has a valid length *)
   valid_aliasKeyTBS_ingredients
     aliasKeyCrt_serialNumber
     aliasKeyCrt_i_common aliasKeyCrt_i_org aliasKeyCrt_i_country
     aliasKeyCrt_s_common aliasKeyCrt_s_org aliasKeyCrt_s_country
     aliasKeyCrt_ku
     riot_version /\
   (* Pre: AliasKeyTBS will have a valid length *)
   valid_aliasKeyCRT_ingredients
     (len_of_aliasKeyTBS
       aliasKeyCrt_serialNumber
       aliasKeyCrt_i_common aliasKeyCrt_i_org aliasKeyCrt_i_country
       aliasKeyCrt_s_common aliasKeyCrt_s_org aliasKeyCrt_s_country
       aliasKeyCrt_ku
       riot_version) /\
   (* Pre: `aliasKeyCRT_buf` has exact size to write AliasKeyCRT *)
   v aliasKeyCRT_len == length_of_aliasKeyCRT
                          (len_of_aliasKeyTBS
                            aliasKeyCrt_serialNumber
                            aliasKeyCrt_i_common aliasKeyCrt_i_org aliasKeyCrt_i_country
                            aliasKeyCrt_s_common aliasKeyCrt_s_org aliasKeyCrt_s_country
                            aliasKeyCrt_ku
                            riot_version)

#restart-solver
let riot_post
  (h0: HS.mem)
  (r: unit)
  (h1: HS.mem)
(* Common Inputs *)
  (cdi : B.lbuffer byte_sec 32)
  (fwid: B.lbuffer byte_sec 32)
  (deviceID_label_len: size_t)
  (deviceID_label: B.lbuffer byte_sec (v deviceID_label_len))
  (aliasKey_label_len: size_t)
  (aliasKey_label: B.lbuffer byte_sec (v aliasKey_label_len))
(* DeviceID CSR Inputs*)
  (deviceIDCSR_ku: key_usage_payload_t)
  (deviceIDCSR_version: datatype_of_asn1_type INTEGER)
  (deviceIDCSR_s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (deviceIDCSR_s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (deviceIDCSR_s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
(* AliasKey Crt Inputs*)
  (aliasKeyCrt_version: x509_version_t)
  (aliasKeyCrt_serialNumber: x509_serialNumber_t)
  (aliasKeyCrt_i_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (aliasKeyCrt_i_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (aliasKeyCrt_i_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (aliasKeyCrt_notBefore: datatype_of_asn1_type Generalized_Time)
  (aliasKeyCrt_notAfter : datatype_of_asn1_type Generalized_Time)
  (aliasKeyCrt_s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (aliasKeyCrt_s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (aliasKeyCrt_s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (aliasKeyCrt_ku: key_usage_payload_t)
  (riot_version: datatype_of_asn1_type INTEGER)
(* Common Outputs *)
  (aliasKey_pub: B.lbuffer byte_pub 32)
  (aliasKey_priv: B.lbuffer uint8 32)
(* DeviceID CSR Outputs *)
  (deviceIDCSR_len: size_t)
  (deviceIDCSR_buf: B.lbuffer byte_pub (v deviceIDCSR_len))
(* AliasKey Crt Outputs *)
  (aliasKeyCRT_len: size_t)
  (aliasKeyCRT_buf: B.lbuffer byte_pub (v aliasKeyCRT_len)
                    { riot_pre
                        (h0)
                        (cdi)
                        (fwid)
                        (deviceID_label_len) (deviceID_label)
                        (aliasKey_label_len) (aliasKey_label)
                        (deviceIDCSR_ku)
                        (deviceIDCSR_version)
                        (deviceIDCSR_s_common) (deviceIDCSR_s_org) (deviceIDCSR_s_country)
                        (aliasKeyCrt_version)
                        (aliasKeyCrt_serialNumber)
                        (aliasKeyCrt_i_common) (aliasKeyCrt_i_org) (aliasKeyCrt_i_country)
                        (aliasKeyCrt_notBefore) (aliasKeyCrt_notAfter)
                        (aliasKeyCrt_s_common) (aliasKeyCrt_s_org) (aliasKeyCrt_s_country)
                        (aliasKeyCrt_ku)
                        (riot_version)
                        (aliasKey_pub)
                        (aliasKey_priv)
                        (deviceIDCSR_len) (deviceIDCSR_buf)
                        (aliasKeyCRT_len) (aliasKeyCRT_buf) })
: Type0
=   (* Post: Modifies *)
     B.(modifies (loc_buffer deviceIDCSR_buf `loc_union`
                  loc_buffer aliasKeyCRT_buf `loc_union`
                  loc_buffer aliasKey_pub    `loc_union`
                  loc_buffer aliasKey_priv ) h0 h1) /\
    (* Post: AliasKey *)
    ((B.as_seq h1 aliasKey_pub  <: lbytes_pub 32),
     (B.as_seq h1 aliasKey_priv <: lbytes_sec 32)) == derive_AliasKey_spec
                                                        (B.as_seq h0 cdi)
                                                        (B.as_seq h0 fwid)
                                                        aliasKey_label_len
                                                        (B.as_seq h0 aliasKey_label) /\
    (* Post: AliasKeyCRT *)
    (let deviceID_pub_seq, deviceID_priv_seq = derive_DeviceID_spec
                                                 (B.as_seq h0 cdi)
                                                 (deviceID_label_len)
                                                 (B.as_seq h0 deviceID_label) in
     let deviceIDCRI: deviceIDCRI_t = create_deviceIDCRI_spec
                                                                         (deviceIDCSR_version)
                                                                         (deviceIDCSR_s_common)
                                                                         (deviceIDCSR_s_org)
                                                                         (deviceIDCSR_s_country)
                                                                         (deviceIDCSR_ku)
                                                                         (deviceID_pub_seq)
                                                                         in
     let deviceIDCRI_seq = serialize_deviceIDCRI `serialize` deviceIDCRI in
     let deviceIDCRI_len = len_of_deviceIDCRI
                             deviceIDCSR_version
                             deviceIDCSR_s_common deviceIDCSR_s_org deviceIDCSR_s_country
                             deviceIDCSR_ku in
     let (* Prf *) _ = lemma_serialize_deviceIDCRI_size_exact deviceIDCRI in
     let deviceIDCSR: deviceIDCSR_t deviceIDCRI_len = sign_and_finalize_deviceIDCSR_spec
                                                                (deviceID_priv_seq)
                                                                (deviceIDCRI_len)
                                                                (deviceIDCRI_seq) in
     let aliasKeyTBS: aliasKeyTBS_t = create_aliasKeyTBS_spec
                                        (aliasKeyCrt_version)
                                        (aliasKeyCrt_serialNumber)
                                        (aliasKeyCrt_i_common) (aliasKeyCrt_i_org) (aliasKeyCrt_i_country)
                                        (aliasKeyCrt_notBefore) (aliasKeyCrt_notAfter)
                                        (aliasKeyCrt_s_common) (aliasKeyCrt_s_org) (aliasKeyCrt_s_country)
                                        (aliasKeyCrt_ku)
                                        (riot_version)
                                        (B.as_seq h0 fwid)
                                        (deviceID_pub_seq)
                                        (B.as_seq h1 aliasKey_pub)
                                        in
     let aliasKeyTBS_seq = serialize_aliasKeyTBS `serialize` aliasKeyTBS in
     let aliasKeyTBS_len = len_of_aliasKeyTBS
                            aliasKeyCrt_serialNumber
                            aliasKeyCrt_i_common aliasKeyCrt_i_org aliasKeyCrt_i_country
                            aliasKeyCrt_s_common aliasKeyCrt_s_org aliasKeyCrt_s_country
                            aliasKeyCrt_ku
                            riot_version in
     let (* Prf *) _ = lemma_serialize_aliasKeyTBS_size_exact aliasKeyTBS in
     let aliasKeyCRT: aliasKeyCRT_t aliasKeyTBS_len = sign_and_finalize_aliasKeyCRT_spec
                                                                (deviceID_priv_seq)
                                                                (aliasKeyTBS_len)
                                                                (aliasKeyTBS_seq) in
     B.as_seq h1 deviceIDCSR_buf == serialize_deviceIDCSR deviceIDCRI_len `serialize` deviceIDCSR /\
     B.as_seq h1 aliasKeyCRT_buf == serialize_aliasKeyCRT aliasKeyTBS_len `serialize` aliasKeyCRT)

#restart-solver
let riot
(* Common Inputs *)
  (cdi : B.lbuffer byte_sec 32)
  (fwid: B.lbuffer byte_sec 32)
  (deviceID_label_len: size_t)
  (deviceID_label: B.lbuffer byte_sec (v deviceID_label_len))
  (aliasKey_label_len: size_t)
  (aliasKey_label: B.lbuffer byte_sec (v aliasKey_label_len))
(* DeviceID CSR Inputs*)
  (deviceIDCSR_ku: key_usage_payload_t)
  (deviceIDCSR_version: datatype_of_asn1_type INTEGER)
  (deviceIDCSR_s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (deviceIDCSR_s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (deviceIDCSR_s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
(* AliasKey Crt Inputs*)
  (aliasKeyCrt_version: x509_version_t)
  (aliasKeyCrt_serialNumber: x509_serialNumber_t)
  (aliasKeyCrt_i_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (aliasKeyCrt_i_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (aliasKeyCrt_i_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (aliasKeyCrt_notBefore: datatype_of_asn1_type Generalized_Time)
  (aliasKeyCrt_notAfter : datatype_of_asn1_type Generalized_Time)
  (aliasKeyCrt_s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (aliasKeyCrt_s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (aliasKeyCrt_s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  (aliasKeyCrt_ku: key_usage_payload_t)
  (riot_version: datatype_of_asn1_type INTEGER)
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
                        (deviceIDCSR_ku)
                        (deviceIDCSR_version)
                        (deviceIDCSR_s_common) (deviceIDCSR_s_org) (deviceIDCSR_s_country)
                        (aliasKeyCrt_version)
                        (aliasKeyCrt_serialNumber)
                        (aliasKeyCrt_i_common) (aliasKeyCrt_i_org) (aliasKeyCrt_i_country)
                        (aliasKeyCrt_notBefore) (aliasKeyCrt_notAfter)
                        (aliasKeyCrt_s_common) (aliasKeyCrt_s_org) (aliasKeyCrt_s_country)
                        (aliasKeyCrt_ku)
                        (riot_version)
                        (aliasKey_pub)
                        (aliasKey_priv)
                        (deviceIDCSR_len) (deviceIDCSR_buf)
                        (aliasKeyCRT_len) (aliasKeyCRT_buf)
   )
   (ensures fun h0 _ h1 -> riot_post
                        (h0) () (h1)
                        (cdi)
                        (fwid)
                        (deviceID_label_len) (deviceID_label)
                        (aliasKey_label_len) (aliasKey_label)
                        (deviceIDCSR_ku)
                        (deviceIDCSR_version)
                        (deviceIDCSR_s_common) (deviceIDCSR_s_org) (deviceIDCSR_s_country)
                        (aliasKeyCrt_version)
                        (aliasKeyCrt_serialNumber)
                        (aliasKeyCrt_i_common) (aliasKeyCrt_i_org) (aliasKeyCrt_i_country)
                        (aliasKeyCrt_notBefore) (aliasKeyCrt_notAfter)
                        (aliasKeyCrt_s_common) (aliasKeyCrt_s_org) (aliasKeyCrt_s_country)
                        (aliasKeyCrt_ku)
                        (riot_version)
                        (aliasKey_pub)
                        (aliasKey_priv)
                        (deviceIDCSR_len) (deviceIDCSR_buf)
                        (aliasKeyCRT_len) (aliasKeyCRT_buf))
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
                                                            deviceIDCSR_version
                                                            deviceIDCSR_s_common
                                                            deviceIDCSR_s_org
                                                            deviceIDCSR_s_country
                                                            deviceIDCSR_ku in
   let deviceIDCRI_buf: B.lbuffer byte_pub (v deviceIDCRI_len) = B.alloca 0x00uy deviceIDCRI_len in

   printf "Creating DeviceID Certificate Signing Request Information\n" done;
   create_deviceIDCRI
    (* version   *) deviceIDCSR_version
                    deviceIDCSR_s_common
                    deviceIDCSR_s_org
                    deviceIDCSR_s_country
    (* key usage *) deviceIDCSR_ku
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
                                                           aliasKeyCrt_serialNumber
                                                           aliasKeyCrt_i_common aliasKeyCrt_i_org aliasKeyCrt_i_country
                                                           aliasKeyCrt_s_common aliasKeyCrt_s_org aliasKeyCrt_s_country
                                                           aliasKeyCrt_ku
                                                           riot_version in
  let aliasKeyTBS_buf: B.lbuffer byte_pub (v aliasKeyTBS_len) = B.alloca 0x00uy aliasKeyTBS_len in

  printf "Creating AliasKey Certificate TBS\n" done;
  create_aliasKeyTBS
    (aliasKeyCrt_version)
    (aliasKeyCrt_serialNumber)
    (aliasKeyCrt_i_common) (aliasKeyCrt_i_org) (aliasKeyCrt_i_country)
    (aliasKeyCrt_notBefore) (aliasKeyCrt_notAfter)
    (aliasKeyCrt_s_common) (aliasKeyCrt_s_org) (aliasKeyCrt_s_country)
    (fwid)
    (aliasKeyCrt_ku)
    (riot_version)
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
