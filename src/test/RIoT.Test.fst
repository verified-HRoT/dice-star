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

let template_len: size_t = 175ul

unfold noextract inline_for_extraction
let template_list: List.llist byte_pub (v template_len)
=
  [@inline_let]let l = [0xA0uy; 0x03uy; 0x02uy; 0x01uy; 0x02uy; 0x02uy; 0x01uy; 0x00uy; 0x30uy; 0x0Duy; 0x06uy; 0x09uy; 0x2Auy; 0x86uy; 0x48uy; 0x86uy; 0xF7uy; 0x0Duy; 0x01uy; 0x01uy; 0x0Duy; 0x05uy; 0x00uy; 0x30uy; 0x3Auy; 0x31uy; 0x0Buy; 0x30uy; 0x09uy; 0x06uy; 0x03uy; 0x55uy; 0x04uy; 0x06uy; 0x13uy; 0x02uy; 0x75uy; 0x73uy; 0x31uy; 0x0Duy; 0x30uy; 0x0Buy; 0x06uy; 0x03uy; 0x55uy; 0x04uy; 0x08uy; 0x0Cuy; 0x04uy; 0x74uy; 0x65uy; 0x73uy; 0x74uy; 0x31uy; 0x0Duy; 0x30uy; 0x0Buy; 0x06uy; 0x03uy; 0x55uy; 0x04uy; 0x0Auy; 0x0Cuy; 0x04uy; 0x74uy; 0x65uy; 0x73uy; 0x74uy; 0x31uy; 0x0Duy; 0x30uy; 0x0Buy; 0x06uy; 0x03uy; 0x55uy; 0x04uy; 0x03uy; 0x0Cuy; 0x04uy; 0x74uy; 0x65uy; 0x73uy; 0x74uy; 0x30uy; 0x1Euy; 0x17uy; 0x0Duy; 0x32uy; 0x30uy; 0x30uy; 0x36uy; 0x32uy; 0x35uy; 0x30uy; 0x32uy; 0x35uy; 0x37uy; 0x30uy; 0x32uy; 0x5Auy; 0x17uy; 0x0Duy; 0x32uy; 0x31uy; 0x30uy; 0x36uy; 0x32uy; 0x35uy; 0x30uy; 0x32uy; 0x35uy; 0x37uy; 0x30uy; 0x32uy; 0x5Auy; 0x30uy; 0x3Auy; 0x31uy; 0x0Buy; 0x30uy; 0x09uy; 0x06uy; 0x03uy; 0x55uy; 0x04uy; 0x06uy; 0x13uy; 0x02uy; 0x75uy; 0x73uy; 0x31uy; 0x0Duy; 0x30uy; 0x0Buy; 0x06uy; 0x03uy; 0x55uy; 0x04uy; 0x08uy; 0x0Cuy; 0x04uy; 0x74uy; 0x65uy; 0x73uy; 0x74uy; 0x31uy; 0x0Duy; 0x30uy; 0x0Buy; 0x06uy; 0x03uy; 0x55uy; 0x04uy; 0x0Auy; 0x0Cuy; 0x04uy; 0x74uy; 0x65uy; 0x73uy; 0x74uy; 0x31uy; 0x0Duy; 0x30uy; 0x0Buy; 0x06uy; 0x03uy; 0x55uy; 0x04uy; 0x03uy; 0x0Cuy; 0x04uy; 0x74uy; 0x65uy; 0x73uy; 0x74uy] in
  assert_norm (List.length l == v template_len);
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
  let version: datatype_of_asn1_type INTEGER = 1l in
  let ku: key_usage_payload_t = aliasKeyCrt_key_usage in

  let template_buf: B.lbuffer byte_pub (v template_len) = B.alloca_of_list template_list in
  let deviceID_lbl_len: x:size_t {normalize (valid_hkdf_lbl_len x)} = 5ul in
  let deviceID_lbl: B.lbuffer byte_sec (v deviceID_lbl_len) = B.alloca (u8 0x00) deviceID_lbl_len in
  let aliasKey_lbl_len: x:size_t {normalize (valid_hkdf_lbl_len x)} = 5ul in
  let aliasKey_lbl: B.lbuffer byte_sec (v aliasKey_lbl_len) = B.alloca (u8 0x00) aliasKey_lbl_len in
  (* Prf *) assert_norm (valid_hkdf_lbl_len deviceID_lbl_len /\ valid_hkdf_lbl_len aliasKey_lbl_len);

  comment "Outputs";
  let aliasKeyCRT_len = len_of_aliasKeyCRT (len_of_aliasKeyTBS template_len ku version) in
  let aliasKeyCRT_buf: B.lbuffer byte_pub (v aliasKeyCRT_len) = B.alloca 0x00uy aliasKeyCRT_len in
  let aliasKey_pub : B.lbuffer byte_pub 32 = B.alloca 0x00uy 32ul in
  let aliasKey_priv: B.lbuffer byte_sec 32 = B.alloca (u8 0x00) 32ul in

  comment "Call riot main function";
  printf "Enter RIoT\n" done;
  riot
    (* cdi       *) cdi
    (* fwid      *) fwid
    (* key usage *) ku
    (* version   *) version
    (* template  *) template_len
                    template_buf
    (* labels    *) deviceID_lbl_len
                    deviceID_lbl
                    aliasKey_lbl_len
                    aliasKey_lbl
    (*aliasKeyCRT*) aliasKeyCRT_len
                    aliasKeyCRT_buf
    (* aliasKey  *) aliasKey_pub
                    aliasKey_priv;
  printf "Exit RIoT\n" done;

  (* Declassify secret buffer to print it *)
  let aliasKey_priv_pub: B.lbuffer byte_pub 32 = B.alloca 0x00uy 32ul in
  declassify_secret_buffer 32ul aliasKey_priv aliasKey_priv_pub;

  printf "AliasKey Public  Key: %xuy \n" 32ul aliasKey_pub  done;
  printf "AliasKey Private Key: %xuy \n" 32ul aliasKey_priv_pub done;
  printf "AliasKey Certificate: %xuy \n" aliasKeyCRT_len aliasKeyCRT_buf done;

  write_out "AliasKeyPublicKey.hex" aliasKey_pub 32ul;
  write_out "AliasKeyPrivateKey.hex" aliasKey_priv_pub 32ul;
  write_out "AliasKeyCrt.hex" aliasKeyCRT_buf aliasKeyCRT_len;

  HST.pop_frame ();
  C.EXIT_SUCCESS
#pop-options
