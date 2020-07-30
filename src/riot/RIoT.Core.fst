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

#restart-solver
#push-options "--query_stats --z3rlimit 1024 --fuel 0 --ifuel 0"
let riot
(* inputs *)
  (cdi : B.lbuffer byte_sec 32)
  (fwid: B.lbuffer byte_sec 32)
  (version: datatype_of_asn1_type INTEGER)
  (aliasKeyTBS_template_len: size_t)
  (aliasKeyTBS_template: B.lbuffer byte_pub (v aliasKeyTBS_template_len))
  (deviceID_label_len: size_t)
  (deviceID_label: B.lbuffer byte_sec (v deviceID_label_len))
  (aliasKey_label_len: size_t)
  (aliasKey_label: B.lbuffer byte_sec (v aliasKey_label_len))
(* outputs *)
  (aliasKeyCRT_len: size_t)
  (aliasKeyCRT_buf: B.lbuffer byte_pub (v aliasKeyCRT_len))
  (aliasKey_pub: B.lbuffer byte_pub 32)
  (aliasKey_priv: B.lbuffer uint8 32)
: HST.Stack unit
  (requires fun h ->
    B.(all_live h [buf cdi;
                   buf fwid;
                   buf aliasKeyTBS_template;
                   buf deviceID_label;
                   buf aliasKey_label;
                   buf aliasKeyCRT_buf;
                   buf aliasKey_pub;
                   buf aliasKey_priv]) /\
    B.(all_disjoint [loc_buffer cdi;
                     loc_buffer fwid;
                     loc_buffer aliasKeyTBS_template;
                     loc_buffer deviceID_label;
                     loc_buffer aliasKey_label;
                     loc_buffer aliasKeyCRT_buf;
                     loc_buffer aliasKey_pub;
                     loc_buffer aliasKey_priv]) /\
   (* Pre: labels have enough length for HKDF *)
   valid_hkdf_lbl_len deviceID_label_len /\
   valid_hkdf_lbl_len aliasKey_label_len /\
   (* Pre: AliasKeyTBS template has a valid length *)
   valid_aliasKeyTBS_ingredients aliasKeyTBS_template_len version /\
   (* Pre: AliasKeyTBS will have a valid length *)
   valid_aliasKeyCRT_ingredients (len_of_AliasKeyTBS aliasKeyTBS_template_len version) /\
   (* Pre: `aliasKeyCRT_buf` has exact size to write AliasKeyCRT *)
   v aliasKeyCRT_len == length_of_AliasKeyCRT (len_of_AliasKeyTBS aliasKeyTBS_template_len version)
   )
   (ensures fun h0 _ h1 ->
    (* Post: Modifies *)
     B.(modifies (loc_buffer aliasKeyCRT_buf `loc_union` loc_buffer aliasKey_pub `loc_union` loc_buffer aliasKey_priv) h0 h1) /\
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
     let aliasKeyTBS: aliasKeyTBS_t_inbound aliasKeyTBS_template_len = create_aliasKeyTBS_spec
                                                                         (aliasKeyTBS_template_len)
                                                                         (B.as_seq h0 aliasKeyTBS_template)
                                                                         (version)
                                                                         (B.as_seq h0 fwid)
                                                                         (deviceID_pub_seq)
                                                                         (B.as_seq h1 aliasKey_pub)
                                                                         in
     let aliasKeyTBS_seq = serialize_aliasKeyTBS_sequence_TLV aliasKeyTBS_template_len `serialize` aliasKeyTBS in
     let aliasKeyTBS_len = len_of_AliasKeyTBS aliasKeyTBS_template_len version in
     (* Prf *) lemma_serialize_aliasKeyTBS_sequence_TLV_size_exact aliasKeyTBS_template_len aliasKeyTBS;
    (let aliasKeyCRT: aliasKeyCRT_t_inbound aliasKeyTBS_len = sign_and_finalize_aliasKeyCRT_spec
                                                                (deviceID_priv_seq)
                                                                (aliasKeyTBS_len)
                                                                (aliasKeyTBS_seq) in
     B.as_seq h1 aliasKeyCRT_buf == serialize_aliasKeyCRT_sequence_TLV aliasKeyTBS_len `serialize` aliasKeyCRT)))
=
 HST.push_frame ();

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

(* Create AliasKeyTBS *)
  let aliasKeyTBS_len: asn1_TLV_int32_of_type SEQUENCE = len_of_AliasKeyTBS aliasKeyTBS_template_len version in
  let aliasKeyTBS_buf: B.lbuffer byte_pub (v aliasKeyTBS_len) = B.alloca 0x00uy aliasKeyTBS_len in

  printf "Creating AliasKey Certificate TBS\n" done;
  create_aliasKeyTBS
    (* FWID      *) fwid
    (* Version   *) version
    (* DeviceID  *) deviceID_pub
    (* AliasKey  *) aliasKey_pub
    (* Template  *) aliasKeyTBS_template_len
                    aliasKeyTBS_template
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
#pop-options

open RIoT.Helpers

let template_len: size_t = 175ul

unfold noextract inline_for_extraction
let template_list: List.llist byte_pub (v template_len)
= [@inline_let]let l = [0xA0uy; 0x03uy; 0x02uy; 0x01uy; 0x02uy; 0x02uy; 0x01uy; 0x00uy; 0x30uy; 0x0Duy; 0x06uy; 0x09uy; 0x2Auy; 0x86uy; 0x48uy; 0x86uy; 0xF7uy; 0x0Duy; 0x01uy; 0x01uy; 0x0Duy; 0x05uy; 0x00uy; 0x30uy; 0x3Auy; 0x31uy; 0x0Buy; 0x30uy; 0x09uy; 0x06uy; 0x03uy; 0x55uy; 0x04uy; 0x06uy; 0x13uy; 0x02uy; 0x75uy; 0x73uy; 0x31uy; 0x0Duy; 0x30uy; 0x0Buy; 0x06uy; 0x03uy; 0x55uy; 0x04uy; 0x08uy; 0x0Cuy; 0x04uy; 0x74uy; 0x65uy; 0x73uy; 0x74uy; 0x31uy; 0x0Duy; 0x30uy; 0x0Buy; 0x06uy; 0x03uy; 0x55uy; 0x04uy; 0x0Auy; 0x0Cuy; 0x04uy; 0x74uy; 0x65uy; 0x73uy; 0x74uy; 0x31uy; 0x0Duy; 0x30uy; 0x0Buy; 0x06uy; 0x03uy; 0x55uy; 0x04uy; 0x03uy; 0x0Cuy; 0x04uy; 0x74uy; 0x65uy; 0x73uy; 0x74uy; 0x30uy; 0x1Euy; 0x17uy; 0x0Duy; 0x32uy; 0x30uy; 0x30uy; 0x36uy; 0x32uy; 0x35uy; 0x30uy; 0x32uy; 0x35uy; 0x37uy; 0x30uy; 0x32uy; 0x5Auy; 0x17uy; 0x0Duy; 0x32uy; 0x31uy; 0x30uy; 0x36uy; 0x32uy; 0x35uy; 0x30uy; 0x32uy; 0x35uy; 0x37uy; 0x30uy; 0x32uy; 0x5Auy; 0x30uy; 0x3Auy; 0x31uy; 0x0Buy; 0x30uy; 0x09uy; 0x06uy; 0x03uy; 0x55uy; 0x04uy; 0x06uy; 0x13uy; 0x02uy; 0x75uy; 0x73uy; 0x31uy; 0x0Duy; 0x30uy; 0x0Buy; 0x06uy; 0x03uy; 0x55uy; 0x04uy; 0x08uy; 0x0Cuy; 0x04uy; 0x74uy; 0x65uy; 0x73uy; 0x74uy; 0x31uy; 0x0Duy; 0x30uy; 0x0Buy; 0x06uy; 0x03uy; 0x55uy; 0x04uy; 0x0Auy; 0x0Cuy; 0x04uy; 0x74uy; 0x65uy; 0x73uy; 0x74uy; 0x31uy; 0x0Duy; 0x30uy; 0x0Buy; 0x06uy; 0x03uy; 0x55uy; 0x04uy; 0x03uy; 0x0Cuy; 0x04uy; 0x74uy; 0x65uy; 0x73uy; 0x74uy] in
  assert_norm (List.length l == v template_len);
  l


#restart-solver
#push-options "--query_stats --z3rlimit 1024 --fuel 0 --ifuel 0"
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

  let template_buf: B.lbuffer byte_pub (v template_len) = B.alloca_of_list template_list in
  let deviceID_lbl_len: x:size_t {normalize (valid_hkdf_lbl_len x)} = 5ul in
  let deviceID_lbl: B.lbuffer byte_sec (v deviceID_lbl_len) = B.alloca (u8 0x00) deviceID_lbl_len in
  let aliasKey_lbl_len: x:size_t {normalize (valid_hkdf_lbl_len x)} = 5ul in
  let aliasKey_lbl: B.lbuffer byte_sec (v aliasKey_lbl_len) = B.alloca (u8 0x00) aliasKey_lbl_len in
  (* Prf *) assert_norm (valid_hkdf_lbl_len deviceID_lbl_len /\ valid_hkdf_lbl_len aliasKey_lbl_len);

  comment "Outputs";
  let aliasKeyCRT_len = len_of_AliasKeyCRT (len_of_AliasKeyTBS template_len version) in
  let aliasKeyCRT_buf: B.lbuffer byte_pub (v aliasKeyCRT_len) = B.alloca 0x00uy aliasKeyCRT_len in
  let aliasKey_pub : B.lbuffer byte_pub 32 = B.alloca 0x00uy 32ul in
  let aliasKey_priv: B.lbuffer byte_sec 32 = B.alloca (u8 0x00) 32ul in

  let x = serialize32_asn1_oid_TLV_backwards () OID_RIOT aliasKeyCRT_buf aliasKeyCRT_len in

  comment "Call riot main function";
  printf "Enter RIoT\n" done;
  riot
    (* cdi       *) cdi
    (* fwid      *) fwid
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
