module RIoT.Test

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

module Ed25519 = Hacl.Ed25519

open RIoT.Test.Definitions

#restart-solver
#push-options "--z3rlimit 256 --fuel 0 --ifuel 0"
let main ()
: HST.ST C.exit_code
  (requires fun h -> True)
  (ensures fun _ _ _ -> True)
=
  HST.push_frame();

  comment "Common Inputs";
  let cdi : B.lbuffer byte_sec 32 = B.alloca (u8 0x00) 32ul in
  let fwid: B.lbuffer byte_sec 32 = B.alloca (u8 0x00) 32ul in
  let riot_version: datatype_of_asn1_type INTEGER = 1l in
  let ku: key_usage_payload_t = aliasKeyCrt_key_usage in

  let deviceID_lbl_len: x:size_t {normalize (valid_hkdf_lbl_len x)} = 5ul in
  let deviceID_lbl: B.lbuffer byte_sec (v deviceID_lbl_len) = B.alloca (u8 0x00) deviceID_lbl_len in
  let aliasKey_lbl_len: x:size_t {normalize (valid_hkdf_lbl_len x)} = 5ul in
  let aliasKey_lbl: B.lbuffer byte_sec (v aliasKey_lbl_len) = B.alloca (u8 0x00) aliasKey_lbl_len in
  (* Prf *) assert_norm (valid_hkdf_lbl_len deviceID_lbl_len /\ valid_hkdf_lbl_len aliasKey_lbl_len);

  comment "DeviceID CSR Inputs";

  (* TODO: replace with version *)
  let deviceIDCSR_version: datatype_of_asn1_type INTEGER = 0l in

  comment "AliasKey Crt Inputs";

  comment "Outputs";
  let deviceIDCSR_len = len_of_deviceIDCSR
                          (len_of_deviceIDCRI
                             deviceIDCSR_version
                             s_common s_org s_country
                             ku) in
  let deviceIDCSR_buf: B.lbuffer byte_pub (v deviceIDCSR_len) = B.alloca 0x00uy deviceIDCSR_len in

  let aliasKeyCRT_len = len_of_aliasKeyCRT
                          (len_of_aliasKeyTBS
                            aliasKeyCrt_serialNumber
                            s_common s_org s_country
                            s_common s_org s_country
                            ku
                            riot_version) in
  let aliasKeyCRT_buf: B.lbuffer byte_pub (v aliasKeyCRT_len) = B.alloca 0x00uy aliasKeyCRT_len in

  let aliasKey_pub : B.lbuffer byte_pub 32 = B.alloca 0x00uy 32ul in
  let aliasKey_priv: B.lbuffer byte_sec 32 = B.alloca (u8 0x00) 32ul in

  comment "Call riot main function";
  printf "Enter RIoT\n" done;
  riot
(* Common Inputs *)
    (* cdi       *) cdi
    (* fwid      *) fwid
    (* labels    *) deviceID_lbl_len
                    deviceID_lbl
                    aliasKey_lbl_len
                    aliasKey_lbl
(* DeviceID CSR Inputs*)
    (* key usage *) ku
                    deviceIDCSR_version
                    s_common
                    s_org
                    s_country
(* AliasKey Crt Inputs*)
    (* version   *) aliasKeyCrt_version
    (*   SN      *) aliasKeyCrt_serialNumber
    (* issuer    *) s_common
                    s_org
                    s_country
    (* validity  *) notBefore
                    notAfter
    (* subject   *) s_common
                    s_org
                    s_country
    (* key usage *) ku
                    riot_version
(* Common Outputs *)
    (* aliasKey  *) aliasKey_pub
                    aliasKey_priv
(* DeviceID CSR Outputs *)
                    deviceIDCSR_len
                    deviceIDCSR_buf
(* AliasKey Crt Outputs *)
    (*aliasKeyCRT*) aliasKeyCRT_len
                    aliasKeyCRT_buf;
  printf "Exit RIoT\n" done;

  (* Declassify secret buffer to print it *)
  let aliasKey_priv_pub: B.lbuffer byte_pub 32 = B.alloca 0x00uy 32ul in
  declassify_secret_buffer 32ul aliasKey_priv aliasKey_priv_pub;

  printf "AliasKey Public  Key: %xuy \n" 32ul aliasKey_pub  done;
  printf "AliasKey Private Key: %xuy \n" 32ul aliasKey_priv_pub done;
  printf "DeviceID CSR        : %xuy \n" deviceIDCSR_len deviceIDCSR_buf done;
  printf "AliasKey Certificate: %xuy \n" aliasKeyCRT_len aliasKeyCRT_buf done;

  write_out "AliasKeyPublicKey.hex" aliasKey_pub 32ul;
  write_out "AliasKeyPrivateKey.hex" aliasKey_priv_pub 32ul;
  write_out "DeviceIDCSR.hex" deviceIDCSR_buf deviceIDCSR_len;
  write_out "AliasKeyCrt.hex" aliasKeyCRT_buf aliasKeyCRT_len;

  HST.pop_frame ();
  C.EXIT_SUCCESS
#pop-options
