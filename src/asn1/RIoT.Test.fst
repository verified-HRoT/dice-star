module RIoT.Test

open LowParse.Low.Base
open LowParse.Low.Combinators

open ASN1.Spec
open ASN1.Low

// module U8 = FStar.UInt8
// module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
// module MB = LowStar.Monotonic.Buffer
module B = LowStar.Buffer
// module Cast = FStar.Int.Cast
module C = C
module B32 = FStar.Bytes

open X509
open RIoT.X509

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
(*)
#restart-solver
#push-options "--query_stats --z3rlimit 128 --initial_fuel 8"
let x509GetAliasCertTBS
  (tbs_len: size_t)
  (tbs: B.lbuffer uint8 (v tbs_len))
  (tbs_pos: size_t)
  (version: datatype_of_asn1_type INTEGER)
  (aliasKeyPub: key_t)
  (deviceKeyPub: key_t)
  (fwid: B.lbuffer uint8 32)
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
   (let compositeDeviceID = x509_get_compositeDeviceID
                            (* version  *) version
                            (* devKeyPub*) (B32.hide (B.as_seq h deviceKeyPub))
                            (* fwid     *) (B32.hide (B.as_seq h fwid)) in
    let subjectPublicKeyInfo = x509_get_public_key_info
                               (* alg *) alg_AliasKey
                               (* pub *) (B32.hide (B.as_seq h aliasKeyPub)) in
    let offset2 = length_of_opaque_serialization serialize_compositeDeviceID_sequence_TLV compositeDeviceID in
    let offset1 = length_of_opaque_serialization (serialize_subjectPublicKeyInfo_sequence_TLV alg_AliasKey) subjectPublicKeyInfo in
    offset1 + offset2 <= v tbs_pos))
  (ensures fun h0 offset32 h1 ->
    v offset32 <= v tbs_pos /\
    B.modifies (B.loc_buffer_from_to tbs (tbs_pos -! offset32) tbs_pos) h0 h1 /\
   (let compositeDeviceID = x509_get_compositeDeviceID
                            (* version  *) version
                            (* devKeyPub*) (B32.hide (B.as_seq h0 deviceKeyPub))
                            (* fwid     *) (B32.hide (B.as_seq h0 fwid)) in
    let subjectPublicKeyInfo = x509_get_public_key_info
                               (* alg *) alg_AliasKey
                               (* pub *) (B32.hide (B.as_seq h0 aliasKeyPub)) in
    Seq.slice (B.as_seq h1 tbs) (v tbs_pos - v offset32) (v tbs_pos) ==
    (serialize_subjectPublicKeyInfo_sequence_TLV alg_AliasKey `serialize` subjectPublicKeyInfo)
    `Seq.append`
    (serialize_compositeDeviceID_sequence_TLV `serialize` compositeDeviceID)))
= let compositeDeviceID = x509_get_compositeDeviceID
                          (* version  *) version
                          (* devKeyPub*) (B32.of_buffer 32ul deviceKeyPub)
                          (* fwid     *) (B32.of_buffer 32ul fwid) in
  let subjectPublicKeyInfo = x509_get_public_key_info
                             (* alg *) alg_AliasKey
                             (* pub *) (B32.of_buffer 32ul (aliasKeyPub)) in
  (* prf *) let h0 = HST.get () in
  let offset2 = serialize32_compositeDeviceID_sequence_TLV_backwards
                (* val *) compositeDeviceID
                 (* buf *) tbs
               (* pos *) tbs_pos in
  (* prf *) let h1 = HST.get () in
  let offset1 = serialize32_subjectPublicKeyInfo_sequence_TLV_backwards
                (* alg *) alg_AliasKey
                (* val *) subjectPublicKeyInfo
                (* buf *) tbs
                (* pos *) (tbs_pos -! offset2) in
  (* prf *) let h2 = HST.get () in
  (* Prf *) B.modifies_buffer_from_to_elim
            (* buf *) tbs
            (*frame*) (tbs_pos -! offset2) (tbs_pos)
            (* new *) (B.loc_buffer_from_to tbs (tbs_pos -! (offset1 +! offset2)) (tbs_pos -! offset2))
            (* mem *) h1 (*to*) h2;
  (* Prf *) Seq.lemma_split (Seq.slice (B.as_seq h2 tbs) (v (tbs_pos -! (offset1 +! offset2))) (v tbs_pos)) (v offset1);
(* return *) offset1 +! offset2
#pop-options

#restart-solver
#push-options "--query_stats --z3rlimit 64"
let main ()
: HST.St C.exit_code
= HST.push_frame ();

  let private_key = B.alloca 0x00uy 32ul in
  let public_key = P256.secretToPublic private_key in

  (* Create TBS region for Alias Key *)
  let buf_len = 500ul in
  let buf = B.alloca 0x00uy buf_len in

  let offset = 50ul in

  let aliasSig = B.alloca 0x00uy 64ul in
  let aliasTBS = B.sub buf (buf_len -! offset) offset in

  ECDSA.ecdsa_p256_sha2_sign
    (* sig *) aliasSig
    (* priv*) private_key
    (* len *) offset
    (* msg *) aliasTBS;

  HST.pop_frame ();
  C.EXIT_SUCCESS
#pop-options
