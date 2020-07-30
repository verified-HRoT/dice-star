/// Reference: https://github.com/microsoft/RIoT/blob/master/Reference/RIoT/Core/RIoT.cpp
module RIoT.Wrap

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
open RIoT.Core
open RIoT.Helpers

module Ed25519 = Hacl.Ed25519

noeq
type l1_params_t = {

    // Full version number of L0 reported by L0
    // versionL0 : uint8;

    // ICU Measurement obtained by L0
    // iCUMeasurement B.lbuffer uint8 32;

    // Storage for Compound Device Identifier
    cdi : B.lbuffer byte_sec 32;

    // Storage for Signing Identity
    sid : B.lbuffer byte_sec 32;
}

noeq
type l2_params_t = {

    // Full version numbers of L0 and L1 reported by each image
    // versionL0 : uint8;
    // versionL1 : uint8;

    // ICU Measurement obtained by L0
    // iCUMeasurement B.lbuffer uint8 32;

    // pSKPub : pubkey_t;
    // deviceID_public_key : pubkey_t;

    // deviceID_cert       : cert: cert_t{
    //    B.(all_disjoint
    //         ([loc_buffer deviceID_public_key]
    //         @(get_cert_loc_l cert)))
    // }

    alias_public_key  : B.lbuffer byte_pub 32;
    alias_private_key : B.lbuffer byte_sec 32;

    aliasKey_crt_len: size_t;
    aliasKey_crt : B.lbuffer byte_pub (v aliasKey_crt_len);

    // char     aliasCert[CC_DER_MAX_PEM];
    // char     deviceCert[CC_DER_MAX_PEM];
    // char     deviceCsr[CC_DER_MAX_PEM];
    // char     pSKCert[CC_DER_MAX_PEM];
    // char     pSKCsr[CC_DER_MAX_PEM];
    // CodeIdentity iCUIdentity;
}


let template_len: size_t = 175ul

unfold noextract inline_for_extraction
let template_list: List.llist byte_pub (v template_len)
= [@inline_let]let l = [0xA0uy; 0x03uy; 0x02uy; 0x01uy; 0x02uy; 0x02uy; 0x01uy; 0x00uy; 0x30uy; 0x0Duy; 0x06uy; 0x09uy; 0x2Auy; 0x86uy; 0x48uy; 0x86uy; 0xF7uy; 0x0Duy; 0x01uy; 0x01uy; 0x0Duy; 0x05uy; 0x00uy; 0x30uy; 0x3Auy; 0x31uy; 0x0Buy; 0x30uy; 0x09uy; 0x06uy; 0x03uy; 0x55uy; 0x04uy; 0x06uy; 0x13uy; 0x02uy; 0x75uy; 0x73uy; 0x31uy; 0x0Duy; 0x30uy; 0x0Buy; 0x06uy; 0x03uy; 0x55uy; 0x04uy; 0x08uy; 0x0Cuy; 0x04uy; 0x74uy; 0x65uy; 0x73uy; 0x74uy; 0x31uy; 0x0Duy; 0x30uy; 0x0Buy; 0x06uy; 0x03uy; 0x55uy; 0x04uy; 0x0Auy; 0x0Cuy; 0x04uy; 0x74uy; 0x65uy; 0x73uy; 0x74uy; 0x31uy; 0x0Duy; 0x30uy; 0x0Buy; 0x06uy; 0x03uy; 0x55uy; 0x04uy; 0x03uy; 0x0Cuy; 0x04uy; 0x74uy; 0x65uy; 0x73uy; 0x74uy; 0x30uy; 0x1Euy; 0x17uy; 0x0Duy; 0x32uy; 0x30uy; 0x30uy; 0x36uy; 0x32uy; 0x35uy; 0x30uy; 0x32uy; 0x35uy; 0x37uy; 0x30uy; 0x32uy; 0x5Auy; 0x17uy; 0x0Duy; 0x32uy; 0x31uy; 0x30uy; 0x36uy; 0x32uy; 0x35uy; 0x30uy; 0x32uy; 0x35uy; 0x37uy; 0x30uy; 0x32uy; 0x5Auy; 0x30uy; 0x3Auy; 0x31uy; 0x0Buy; 0x30uy; 0x09uy; 0x06uy; 0x03uy; 0x55uy; 0x04uy; 0x06uy; 0x13uy; 0x02uy; 0x75uy; 0x73uy; 0x31uy; 0x0Duy; 0x30uy; 0x0Buy; 0x06uy; 0x03uy; 0x55uy; 0x04uy; 0x08uy; 0x0Cuy; 0x04uy; 0x74uy; 0x65uy; 0x73uy; 0x74uy; 0x31uy; 0x0Duy; 0x30uy; 0x0Buy; 0x06uy; 0x03uy; 0x55uy; 0x04uy; 0x0Auy; 0x0Cuy; 0x04uy; 0x74uy; 0x65uy; 0x73uy; 0x74uy; 0x31uy; 0x0Duy; 0x30uy; 0x0Buy; 0x06uy; 0x03uy; 0x55uy; 0x04uy; 0x03uy; 0x0Cuy; 0x04uy; 0x74uy; 0x65uy; 0x73uy; 0x74uy] in
  assert_norm (List.length l == v template_len);
  l



let riot_wrap
  (l2_base: B.buffer uint8)
  (l2_size: size_t)
  (l1_params: l1_params_t)
  (l2_params: l2_params_t)
: HST.Stack unit
  (requires fun h ->
    B.(all_live h [buf l2_base;
                   buf l1_params.cdi;
                   buf l1_params.sid;
                   buf l2_params.alias_public_key;
                   buf l2_params.alias_private_key;
                   buf l2_params.aliasKey_crt]) /\
    B.(all_disjoint [loc_buffer l2_base;
                     loc_buffer l1_params.cdi;
                     loc_buffer l1_params.sid;
                     loc_buffer l2_params.alias_public_key;
                     loc_buffer l2_params.alias_private_key;
                     loc_buffer l2_params.aliasKey_crt]) /\
    B.length l2_base == v l2_size
                     )
  (ensures fun h0 _ h1 -> True)
=
  let template_buf: B.lbuffer byte_pub (v template_len) = B.alloca_of_list template_list in

  // TODO:
  let fwid: B.lbuffer byte_sec 32 = B.alloca (u8 0x00) 32ul in
  let version: datatype_of_asn1_type INTEGER = 1l in
  let deviceID_lbl_len: x:size_t {normalize (valid_hkdf_lbl_len x)} = 5ul in
  let deviceID_lbl: B.lbuffer byte_sec (v deviceID_lbl_len) = B.alloca (u8 0x00) deviceID_lbl_len in
  let aliasKey_lbl_len: x:size_t {normalize (valid_hkdf_lbl_len x)} = 5ul in
  let aliasKey_lbl: B.lbuffer byte_sec (v aliasKey_lbl_len) = B.alloca (u8 0x00) aliasKey_lbl_len in
  (* Prf *) assert_norm (valid_hkdf_lbl_len deviceID_lbl_len /\ valid_hkdf_lbl_len aliasKey_lbl_len);

  riot
    (* cdi       *) l1_params.cdi
    (* fwid      *) fwid
    (* version   *) version
    (* template  *) template_len
                    template_buf
    (* labels    *) deviceID_lbl_len
                    deviceID_lbl
                    aliasKey_lbl_len
                    aliasKey_lbl
    (*aliasKeyCRT*) l2_params.aliasKey_crt_len
                    l2_params.aliasKey_crt
    (* aliasKey  *) l2_params.alias_public_key
                    l2_params.alias_private_key

(*)
