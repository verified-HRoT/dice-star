module RIoT.Test

open LowParse.Low.Base
open LowParse.Low.Combinators

open ASN1.Spec
open ASN1.Low

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module MB = LowStar.Monotonic.Buffer
module B = LowStar.Buffer
module Cast = FStar.Int.Cast
module C = C
module B32 = FStar.Bytes
open RIoT.Ext

open Lib.IntTypes
friend Lib.IntTypes

module I = FStar.Integers

(* TODO: Will replace this with a full test after I finished the
         length spec/impl for SEQUENCE TLV (tomorrow).*)
#restart-solver
#push-options "--z3rlimit 64"
let main ()
: HST.St C.exit_code
= HST.push_frame ();

  let algo_oid: b: B.buffer uint8 {B.length b == 2} = B.alloca 0x05uy 2ul in
  let algo_param: b: B.buffer uint8 {B.length b == 5} = B.alloca 0x01uy 5ul in
  let algo_id: algorithmIdentifier_t = {
    algorithm_oid = (|2ul, B32.of_buffer 2ul algo_oid|);
    parameters    = (|5ul, B32.of_buffer 5ul algo_param|)
  } in

  (* NOTE: We need to prove this whole constructed SEQUENCE value has a valid length frist. *)
  (* Prf *) serialize_algorithmIdentifier_value_unfold algo_id;
  (* Prf *) serialize_asn1_octet_string_TLV_size algo_id.algorithm_oid;
  (* Prf *) serialize_asn1_octet_string_TLV_size algo_id.parameters;

  (* NOTE: Then reveal the whole constructed SEQUENCE TLV's length. *)
  // (* Prf *) serialize_algorithmIdentifier_sequence_unfold algo_id;
  (* Prf *) serialize_algorithmIdentifier_sequence_TLV_size algo_id;

  let pubkey: b: B.buffer uint8 {B.length b == 3} = B.alloca 0b100uy 3ul in
  let subjectPublicKeyInfo: subjectPublicKeyInfo_t = {
    algorithm = algo_id;
    subjectPublicKey = (|4ul, 2ul, B32.of_buffer 3ul pubkey|)
  } in

  (* NOTE: Prove subjectPublicKeyInfo is inbound. *)
  (* Prf *) serialize_subjectPublicKeyInfo_value_unfold subjectPublicKeyInfo;
  (* Prf *) serialize_asn1_bit_string_TLV_size subjectPublicKeyInfo.subjectPublicKey;

  (* NOTE: Reveal subjectPublicKeyInfo's TLV's length. *)
  (* Prf *) serialize_subjectPublicKeyInfo_sequence_TLV_size subjectPublicKeyInfo;

  let dst: b: B.buffer pub_uint8 {B.length b == 100} = B.alloca 0x00uy 100ul in
  let offset = serialize32_subjectPublicKeyInfo_sequence_TLV_backwards
               (* val *) subjectPublicKeyInfo
               (* buf *) dst
               (* pos *) 99ul in

  HST.pop_frame ();
  C.EXIT_SUCCESS
#pop-options
