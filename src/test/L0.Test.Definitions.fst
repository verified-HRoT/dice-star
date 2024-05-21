(* NOTE: Separating this module because verification
         with L0.* loaded becomes expensive *)
module L0.Test.Definitions

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

open L0.Base
open L0.X509.Base
open L0.Declassify
open L0.Helpers
// open L0.Spec
// open L0.Impl
// open L0.Core

module Ed25519 = Hacl.Ed25519

#set-options "--z3rlimit 64 --fuel 0 --ifuel 0 --using_facts_from '* -FStar.Tactics -FStar.Reflection'"

[@@ "opaque_to_smt"]
inline_for_extraction
let dump_l0
  (deviceID_pub : B.lbuffer byte_pub 32)
  (aliasKey_pub : B.lbuffer byte_pub 32)
  (aliasKey_priv: B.lbuffer byte_sec 32)
  (deviceIDCSR_len: UInt32.t)
  (deviceIDCSR_buf: B.lbuffer byte_pub (v deviceIDCSR_len))
  (aliasKeyCRT_len: UInt32.t)
  (aliasKeyCRT_buf: B.lbuffer byte_pub (v aliasKeyCRT_len))
: HST.Stack unit
  (requires fun h ->
    B.all_live h [B.buf deviceID_pub; B.buf aliasKey_pub; B.buf aliasKey_priv; B.buf deviceIDCSR_buf; B.buf aliasKeyCRT_buf])
  (ensures fun h0 _ h1 ->
    B.modifies B.loc_none h0 h1)
= HST.push_frame ();
  let aliasKey_priv_pub: B.lbuffer byte_pub 32 = B.alloca 0x00uy 32ul in
  declassify_secret_buffer 32ul aliasKey_priv aliasKey_priv_pub;

  write_out "DeviceIDPublicKey.hex"  aliasKey_pub 32ul;
  write_out "AliasKeyPublicKey.hex"  aliasKey_pub 32ul;
  write_out "AliasKeyPrivateKey.hex" aliasKey_priv_pub 32ul;
  write_out "DeviceIDCSR.hex" deviceIDCSR_buf deviceIDCSR_len;
  write_out "AliasKeyCrt.hex" aliasKeyCRT_buf aliasKeyCRT_len;
  HST.pop_frame ()
