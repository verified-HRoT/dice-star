module L0.Test

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

open L0.X509
open L0.Base
open L0.Declassify
open L0.Helpers
open L0.Spec
open L0.Impl
open L0.Core
open L0.X509.Sample

module Ed25519 = Hacl.Ed25519

open L0.Test.Definitions

#restart-solver
#push-options "--z3rlimit 1024 --fuel 0 --ifuel 0 --using_facts_from '* -FStar.Tactics -FStar.Reflection -LowParse'"

let main ()
: HST.ST C.exit_code
  (requires fun h -> True)
  (ensures fun _ _ _ -> True)
=
  HST.push_frame();

  comment "Common Inputs";
  let cdi : B.lbuffer byte_sec 32 = B.alloca (u8 0x00) 32ul in
  let fwid: B.lbuffer byte_pub 32 = B.alloca 0uy 32ul in

  let deviceID_lbl_len: x:size_t {normalize (valid_hkdf_lbl_len x)} = 5ul in
  let deviceID_lbl: B.lbuffer byte_pub (v deviceID_lbl_len) = B.alloca 0uy deviceID_lbl_len in
  let aliasKey_lbl_len: x:size_t {normalize (valid_hkdf_lbl_len x)} = 5ul in
  let aliasKey_lbl: B.lbuffer byte_pub (v aliasKey_lbl_len) = B.alloca 0uy aliasKey_lbl_len in
  (* Prf *) assert_norm (valid_hkdf_lbl_len deviceID_lbl_len /\ valid_hkdf_lbl_len aliasKey_lbl_len);

  comment "DeviceID CSR Inputs";
  let deviceIDCSR_ingredients = l0_get_deviceIDCSR_ingredients () in

  comment "AliasKey Crt Inputs";
  let aliasKeyCRT_ingredients = l0_get_aliasKeyCRT_ingredients () in

  comment "Outputs";
  let deviceIDCSR_len = len_of_deviceIDCSR (len_of_deviceIDCRI
                             deviceIDCSR_ingredients.deviceIDCSR_version
                             deviceIDCSR_ingredients.deviceIDCSR_s_common
                             deviceIDCSR_ingredients.deviceIDCSR_s_org
                             deviceIDCSR_ingredients.deviceIDCSR_s_country) in
  let deviceIDCSR_buf: B.lbuffer byte_pub (v deviceIDCSR_len) = B.alloca 0x00uy deviceIDCSR_len in

  let aliasKeyCRT_len = len_of_aliasKeyCRT (len_of_aliasKeyTBS
                            aliasKeyCRT_ingredients.aliasKeyCrt_serialNumber
                            aliasKeyCRT_ingredients.aliasKeyCrt_i_common
                            aliasKeyCRT_ingredients.aliasKeyCrt_i_org
                            aliasKeyCRT_ingredients.aliasKeyCrt_i_country
                            aliasKeyCRT_ingredients.aliasKeyCrt_s_common
                            aliasKeyCRT_ingredients.aliasKeyCrt_s_org
                            aliasKeyCRT_ingredients.aliasKeyCrt_s_country
                            aliasKeyCRT_ingredients.aliasKeyCrt_l0_version) in
  let aliasKeyCRT_buf: B.lbuffer byte_pub (v aliasKeyCRT_len) = B.alloca 0x00uy aliasKeyCRT_len in
  printf "aliasKeyCRT_len: %ul\n" (aliasKeyCRT_len <: UInt32.t) done;
admit();
  let deviceID_pub : B.lbuffer byte_pub 32 = B.alloca 0x00uy 32ul in
  let aliasKey_pub : B.lbuffer byte_pub 32 = B.alloca 0x00uy 32ul in
  let aliasKey_priv: B.lbuffer byte_sec 32 = B.alloca (u8 0x00) 32ul in
admit();
  comment "Call l0 main function";
  printf "Enter L0\n" done;
  l0
(* Common Inputs *)
    (* cdi       *) cdi
    (* fwid      *) fwid
    (* labels    *) deviceID_lbl_len
                    deviceID_lbl
                    aliasKey_lbl_len
                    aliasKey_lbl
(* DeviceID CSR Inputs*)
                    deviceIDCSR_ingredients
(* AliasKey Crt Inputs*)
                    aliasKeyCRT_ingredients
(* Common Outputs *)
    (* deviceID  *) deviceID_pub
    (* aliasKey  *) aliasKey_pub
                    aliasKey_priv
(* DeviceID CSR Outputs *)
                    deviceIDCSR_len
                    deviceIDCSR_buf
(* AliasKey Crt Outputs *)
    (*aliasKeyCRT*) aliasKeyCRT_len
                    aliasKeyCRT_buf;
  printf "Exit L0\n" done;

  dump_l0
    deviceID_pub
    aliasKey_pub
    aliasKey_priv
    deviceIDCSR_len
    deviceIDCSR_buf
    aliasKeyCRT_len
    aliasKeyCRT_buf;

  HST.pop_frame ();
  C.EXIT_SUCCESS
#pop-options
