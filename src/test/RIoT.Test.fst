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

open RIoT.Helpers

#set-options "--z3rlimit 32 --fuel 0 --ifuel 0"

let aliasKeyTBS_template_len: size_t = 175ul

unfold noextract inline_for_extraction
let aliasKeyTBS_template_list: List.llist byte_pub (v aliasKeyTBS_template_len)
=
  [@inline_let]let l = [0xA0uy; 0x03uy; 0x02uy; 0x01uy; 0x02uy; 0x02uy; 0x01uy; 0x00uy; 0x30uy; 0x0Duy; 0x06uy; 0x09uy; 0x2Auy; 0x86uy; 0x48uy; 0x86uy; 0xF7uy; 0x0Duy; 0x01uy; 0x01uy; 0x0Duy; 0x05uy; 0x00uy; 0x30uy; 0x3Auy; 0x31uy; 0x0Buy; 0x30uy; 0x09uy; 0x06uy; 0x03uy; 0x55uy; 0x04uy; 0x06uy; 0x13uy; 0x02uy; 0x75uy; 0x73uy; 0x31uy; 0x0Duy; 0x30uy; 0x0Buy; 0x06uy; 0x03uy; 0x55uy; 0x04uy; 0x08uy; 0x0Cuy; 0x04uy; 0x74uy; 0x65uy; 0x73uy; 0x74uy; 0x31uy; 0x0Duy; 0x30uy; 0x0Buy; 0x06uy; 0x03uy; 0x55uy; 0x04uy; 0x0Auy; 0x0Cuy; 0x04uy; 0x74uy; 0x65uy; 0x73uy; 0x74uy; 0x31uy; 0x0Duy; 0x30uy; 0x0Buy; 0x06uy; 0x03uy; 0x55uy; 0x04uy; 0x03uy; 0x0Cuy; 0x04uy; 0x74uy; 0x65uy; 0x73uy; 0x74uy; 0x30uy; 0x1Euy; 0x17uy; 0x0Duy; 0x32uy; 0x30uy; 0x30uy; 0x36uy; 0x32uy; 0x35uy; 0x30uy; 0x32uy; 0x35uy; 0x37uy; 0x30uy; 0x32uy; 0x5Auy; 0x17uy; 0x0Duy; 0x32uy; 0x31uy; 0x30uy; 0x36uy; 0x32uy; 0x35uy; 0x30uy; 0x32uy; 0x35uy; 0x37uy; 0x30uy; 0x32uy; 0x5Auy; 0x30uy; 0x3Auy; 0x31uy; 0x0Buy; 0x30uy; 0x09uy; 0x06uy; 0x03uy; 0x55uy; 0x04uy; 0x06uy; 0x13uy; 0x02uy; 0x75uy; 0x73uy; 0x31uy; 0x0Duy; 0x30uy; 0x0Buy; 0x06uy; 0x03uy; 0x55uy; 0x04uy; 0x08uy; 0x0Cuy; 0x04uy; 0x74uy; 0x65uy; 0x73uy; 0x74uy; 0x31uy; 0x0Duy; 0x30uy; 0x0Buy; 0x06uy; 0x03uy; 0x55uy; 0x04uy; 0x0Auy; 0x0Cuy; 0x04uy; 0x74uy; 0x65uy; 0x73uy; 0x74uy; 0x31uy; 0x0Duy; 0x30uy; 0x0Buy; 0x06uy; 0x03uy; 0x55uy; 0x04uy; 0x03uy; 0x0Cuy; 0x04uy; 0x74uy; 0x65uy; 0x73uy; 0x74uy] in
  assert_norm (List.length l == v aliasKeyTBS_template_len);
  l

let deviceIDCRI_template_len: size_t = 41ul

unfold noextract inline_for_extraction
let deviceIDCRI_template_list: List.llist byte_pub (v deviceIDCRI_template_len)
= [@inline_let]let l = [0x30uy; 0x27uy; 0x31uy; 0x0Buy; 0x30uy; 0x09uy; 0x06uy; 0x03uy; 0x55uy; 0x04uy; 0x06uy; 0x13uy; 0x02uy; 0x44uy; 0x45uy; 0x31uy; 0x18uy; 0x30uy; 0x16uy; 0x06uy; 0x03uy; 0x55uy; 0x04uy; 0x03uy; 0x0Cuy; 0x0Fuy; 0x77uy; 0x77uy; 0x77uy; 0x2Euy; 0x65uy; 0x78uy; 0x61uy; 0x6Duy; 0x70uy; 0x6Cuy; 0x65uy; 0x2Euy; 0x63uy; 0x6Fuy; 0x6Duy] in
  assert_norm (List.length l == v deviceIDCRI_template_len);
  l

#restart-solver
#push-options "--z3rlimit 1024 --fuel 0 --ifuel 0"
let main ()
: HST.ST C.exit_code
  (requires fun h -> True)
  (ensures fun _ _ _ -> True)
=
  HST.push_frame();

  comment "Inputs";
  let cdi : B.lbuffer byte_sec 32 = B.alloca (u8 0x00) 32ul in
  let fwid: B.lbuffer byte_sec 32 = B.alloca (u8 0x00) 32ul in
  let riot_version: datatype_of_asn1_type INTEGER = 1l in
  let deviceIDCSR_version: datatype_of_asn1_type INTEGER = 0l in
  let ku: key_usage_payload_t = aliasKeyCrt_key_usage in

  let deviceIDCRI_template_buf: B.lbuffer byte_pub (v deviceIDCRI_template_len) = B.alloca_of_list deviceIDCRI_template_list in
  let aliasKeyTBS_template_buf: B.lbuffer byte_pub (v aliasKeyTBS_template_len) = B.alloca_of_list aliasKeyTBS_template_list in
  let deviceID_lbl_len: x:size_t {normalize (valid_hkdf_lbl_len x)} = 5ul in
  let deviceID_lbl: B.lbuffer byte_sec (v deviceID_lbl_len) = B.alloca (u8 0x00) deviceID_lbl_len in
  let aliasKey_lbl_len: x:size_t {normalize (valid_hkdf_lbl_len x)} = 5ul in
  let aliasKey_lbl: B.lbuffer byte_sec (v aliasKey_lbl_len) = B.alloca (u8 0x00) aliasKey_lbl_len in
  (* Prf *) assert_norm (valid_hkdf_lbl_len deviceID_lbl_len /\ valid_hkdf_lbl_len aliasKey_lbl_len);

  comment "Outputs";
  let deviceIDCSR_len = len_of_deviceIDCSR (len_of_deviceIDCRI deviceIDCRI_template_len deviceIDCSR_version ku) in
  let deviceIDCSR_buf: B.lbuffer byte_pub (v deviceIDCSR_len) = B.alloca 0x00uy deviceIDCSR_len in
  let aliasKeyCRT_len = len_of_aliasKeyCRT (len_of_aliasKeyTBS aliasKeyTBS_template_len ku riot_version) in
  let aliasKeyCRT_buf: B.lbuffer byte_pub (v aliasKeyCRT_len) = B.alloca 0x00uy aliasKeyCRT_len in
  let aliasKey_pub : B.lbuffer byte_pub 32 = B.alloca 0x00uy 32ul in
  let aliasKey_priv: B.lbuffer byte_sec 32 = B.alloca (u8 0x00) 32ul in

  let deviceIDCSR_version: datatype_of_asn1_type INTEGER = 0l in

  comment "Call riot main function";
  printf "Enter RIoT\n" done;
  riot
    (* cdi       *) cdi
    (* fwid      *) fwid
    (* labels    *) deviceID_lbl_len
                    deviceID_lbl
                    aliasKey_lbl_len
                    aliasKey_lbl

                    ku
                    deviceIDCSR_version
                    deviceIDCRI_template_len
                    deviceIDCRI_template_buf

    (* key usage *) ku
    (* version   *) riot_version
    (* template  *) aliasKeyTBS_template_len
                    aliasKeyTBS_template_buf

    (* aliasKey  *) aliasKey_pub
                    aliasKey_priv

                    deviceIDCSR_len
                    deviceIDCSR_buf

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