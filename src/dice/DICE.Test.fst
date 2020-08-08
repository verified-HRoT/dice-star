module DICE.Test

open LowStar.Comment

module Fail = LowStar.Failure
module B = LowStar.Buffer
module HS  = FStar.HyperStack
module HST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.ByteBuffer
module S = Spec.Hash.Definitions
module Ed25519 = Hacl.Ed25519

module HW = HWAbstraction

open DICE.Definitions
open DICE.Core

let main ()
: HST.ST C.exit_code
  (requires fun h -> HW.uds_is_enabled h)
  (ensures fun _ _ _ -> True)
= HST.push_frame ();

  (* Prf *) HST.recall HW.hwi_state; (* for liveness *)

  let cdi: B.lbuffer byte_sec (v digest_len) = B.alloca (u8 0x00) digest_len in

  let ret = dice_main cdi in

  HST.pop_frame ();
  C.EXIT_SUCCESS
