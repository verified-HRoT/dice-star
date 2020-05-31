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

open X509.Crypto
open X509.RIoT

open Lib.IntTypes
friend Lib.IntTypes

module I = FStar.Integers

module S = Spec.Hash.Definitions
module H = Hacl.Hash.Definitions
// module Ed25519 = Hacl.Ed25519
// module Curve25519 = Hacl.Curve25519_51
module ECDSA = Hacl.Impl.ECDSA
module P256 = Hacl.Impl.P256
module HKDF = Hacl.HKDF

let key_t = B.lbuffer uint8 32
let sig_t = B.lbuffer uint8 64

(* ZT: Some tests to indicate if the proof performance has been
       affected by some definitions from ASN1.* or Hacl.* *)
let _ = assert (length_of_oid OID_EC_GRP_SECP256R1 == 6)
let _ = assert (length_of_asn1_primitive_TLV (Mkbit_string_t 33ul 0ul (magic())) == 35)


#restart-solver
#push-options "--query_stats --z3rlimit 32"
let x509GetAliasCertTBS
  (tbs_len: size_t)
  (tbs: B.lbuffer uint8 (v tbs_len))
  (tbs_pos: size_t)
  (version: datatype_of_asn1_type INTEGER)
  (aliasKeyPub: key_t)
  (deviceKeyPub: key_t)
  (fwid_len: asn1_value_int32_of_type OCTET_STRING)
  (fwid: B.lbuffer uint8 (v fwid_len))
: HST.StackInline (size_t)
  (requires fun h ->
    B.all_live h [B.buf tbs;
                  B.buf aliasKeyPub;
                  B.buf deviceKeyPub;
                  B.buf fwid] /\
    B.all_disjoint [B.loc_buffer tbs;
                    B.loc_buffer aliasKeyPub;
                    B.loc_buffer deviceKeyPub;
                    B.loc_buffer fwid] /\
    0 <= v tbs_pos /\ v tbs_pos <= v tbs_len /\
    v fwid_len < asn1_length_max - 86 /\
   (let compositeDeviceID = constructCompositeDeviceID
                            (* version  *) version
                            (* devKeyPub*) (B32.hide (B.as_seq h deviceKeyPub))
                            (* fwid_len *) fwid_len
                            (* fwid     *) (B32.hide (B.as_seq h fwid)) in
    let offset = Seq.length (serialize serialize_compositeDeviceID_sequence_TLV compositeDeviceID) in
    offset <= v tbs_pos))
  (ensures fun h0 offset h1 ->
    B.modifies (B.loc_buffer_from_to tbs (tbs_pos -! offset) tbs_pos) h0 h1 (* TODO: refine locs *))
= let compositeDeviceID = constructCompositeDeviceID
                          (* version  *) version
                          (* devKeyPub*) (B32.of_buffer 32ul deviceKeyPub)
                          (* fwid_len *) fwid_len
                          (* fwid     *) (B32.of_buffer fwid_len fwid) in
  let offset = serialize32_compositeDeviceID_TLV_sequence_backwards
               (* val *) compositeDeviceID
               (* buf *) tbs
               (* pos *) tbs_pos in
  let aliasPubKeyInfo = x509GetAliasKeyInfo (B32.of_buffer 32ul aliasKeyPub) in
offset
#pop-options

let () = ()


#restart-solver
#push-options "--query_stats --z3rlimit 64"
let main ()
: HST.St C.exit_code
= HST.push_frame ();

  let private_key = B.alloca 0x00uy 32ul in
  let public_key = Ed25519.secret_to_public private_key in

  (* Create TBS region for Alias Key *)
  let buf_len = 500ul in
  let buf = B.alloca 0x00uy buf_len in

  // let algo_oid: b: B.buffer uint8 {B.length b == 2} = B.alloca 0x05uy 2ul in
  // let algo_param: b: B.buffer uint8 {B.length b == 5} = B.alloca 0x01uy 5ul in
  // let algo_id: algorithmIdentifier_t = {
  //   algorithm_oid = (|2ul, B32.of_buffer 2ul algo_oid|);
  //   parameters    = (|5ul, B32.of_buffer 5ul algo_param|)
  // } in

  //   (* NOTE: We need to prove this whole constructed SEQUENCE value has a valid length frist. *)
  // (* Prf *) serialize_algorithmIdentifier_value_unfold algo_id;
  // (* Prf *) lemma_serialize_asn1_octet_string_TLV_size algo_id.algorithm_oid;
  // (* Prf *) lemma_serialize_asn1_octet_string_TLV_size algo_id.parameters;

  // (* NOTE: Then reveal the whole constructed SEQUENCE TLV's length. *)
  // // (* Prf *) serialize_algorithmIdentifier_sequence_unfold algo_id;
  // (* Prf *) serialize_algorithmIdentifier_sequence_TLV_size algo_id;

  // let pubkey: b: B.buffer uint8 {B.length b == 3} = B.alloca 0b100uy 3ul in
  // let subjectPublicKeyInfo: subjectPublicKeyInfo_t = {
  //   algorithm = algo_id;
  //                      (* FIXME: conflicting with `LowParse.Slice.slice` *)
  //   subjectPublicKey = Mkbit_string_t 4ul 2ul (B32.of_buffer 3ul pubkey)
  // } in

  // (* NOTE: Prove subjectPublicKeyInfo is inbound. *)
  // (* Prf *) serialize_subjectPublicKeyInfo_value_unfold subjectPublicKeyInfo;
  // (* Prf *) lemma_serialize_asn1_bit_string_TLV_size subjectPublicKeyInfo.subjectPublicKey;

  // (* NOTE: Reveal subjectPublicKeyInfo's TLV's length. *)
  // (* Prf *) serialize_subjectPublicKeyInfo_sequence_TLV_size subjectPublicKeyInfo;

  // let offset = serialize32_subjectPublicKeyInfo_sequence_TLV_backwards
  //              (* val *) subjectPublicKeyInfo
  //              (* buf *) buf
  //              (* pos *) buf_len in

  let offset = 50ul in

  let aliasSig = B.alloca 0x00uy 64ul in
  let aliasTBS = B.sub buf (buf_len -! offset) offset in

  Ed25519.sign
    (* sig *) aliasSig
    (* priv*) private_key
    (* len *) offset
    (* msg *) aliasTBS;

  HST.pop_frame ();
  C.EXIT_SUCCESS
#pop-options
