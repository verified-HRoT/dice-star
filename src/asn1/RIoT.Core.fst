/// Reference: https://github.com/microsoft/RIoT/blob/master/Reference/RIoT/Core/RIoT.cpp
module RIoT.Core

open LowStar.Comment

module Fail = LowStar.Failure
module B = LowStar.Buffer
module IB = LowStar.ImmutableBuffer
module HS  = FStar.HyperStack
module HST = FStar.HyperStack.ST

open Lib.IntTypes
module S = Spec.Hash.Definitions
module H = Hacl.Hash.Definitions

module ECDSA = Hacl.Impl.ECDSA
module P256 = Hacl.Impl.P256
module Ed25519 = Hacl.Ed25519
module Curve25519 = Hacl.Curve25519_51
module HKDF = Hacl.HKDF

// module HW = HWAbstraction

open S
open H
open RIoT.Definitions

open ASN1.Spec
open ASN1.Low
open X509
open RIoT.X509
open RIoT.Base
open RIoT.Declassify

module B32 = FStar.Bytes

#set-options "--query_stats --z3rlimit 16 --initial_fuel 8 --initial_ifuel 2"
let _ = assert (length_of_oid OID_EC_GRP_SECP256R1 == 6)

// let salt_len: a:size_t{(v a) > 0 /\ Spec.Agile.HMAC.keysized alg (v a)}
//   = 32ul
// (* ZT: Hacl.HKDF.fsti and Spec.Agile.HKDF.fsti
//        have different spec, I choose the smaller
//        one `pow2 32` here*)
// let info_len: a:size_t{(v a) > 0 /\ hash_length SHA2_256 + v a + 1 + block_length SHA2_256 <= pow2 32}
//   = 32ul
// let okm_len : a:size_t{(v a) > 0}
//   = 32ul


#push-options "--z3rlimit 32"
let riot_label_DeviceID: ib:IB.libuffer uint8 2 (Seq.createL [u8 0; u8 0])
                         { IB.frameOf ib == HS.root /\
                           IB.recallable ib /\
                           valid_hkdf_lbl_len (B.len ib) }
= assert_norm (valid_hkdf_lbl_len 2ul);
  IB.igcmalloc_of_list HS.root [u8 0; u8 0]

let riot_label_AliasKey: ib:IB.libuffer uint8 2 (Seq.createL [u8 1; u8 1])
                         { IB.frameOf ib == HS.root /\
                           IB.recallable ib /\
                           valid_hkdf_lbl_len (B.len ib) }
= assert_norm (valid_hkdf_lbl_len 2ul);
  IB.igcmalloc_of_list HS.root [u8 1; u8 1]
#push-options
// assume val s: Seq.lseq uint8 3
// let x: B32.lbytes32 3ul = B32.hide s


let valid_ed25519_sign_mag_length
  (l: nat)
= 64 + l <= max_size_t

#restart-solver
#push-options "--query_stats --z3rlimit 32 --fuel 4 --ifuel 2"
let riot_main
  (cdi : B.lbuffer uint8 32)
  (fwid: B.lbuffer uint8 32)
  (riot_ver: datatype_of_asn1_type INTEGER)
  (aliasKey_crt_len: size_t)
  (aliasKey_crt_pos: size_t)
  (aliasKey_crt: B.lbuffer pub_uint8 (v aliasKey_crt_len))
  (aliasKey_pub: B.lbuffer pub_uint8 32)
  (aliasKey_priv: B.lbuffer uint8 32)
: HST.Stack unit
  (requires fun h ->
    B.(all_live h [buf cdi;
                   buf fwid;
                   buf aliasKey_pub;
                   buf aliasKey_priv;
                   buf aliasKey_crt]) /\
    B.(all_disjoint [loc_buffer cdi;
                     loc_buffer fwid;
                     loc_buffer aliasKey_pub;
                     loc_buffer aliasKey_priv;
                     loc_buffer aliasKey_crt]) /\
    (* pre *) 0 <= v aliasKey_crt_pos /\ v aliasKey_crt_pos <= v aliasKey_crt_len /\
   (let deviceID_pub, deviceID_priv = riot_derive_DeviceID_spec
                                        (B.as_seq h cdi)
                                        (B.len riot_label_DeviceID)
                                        (B.as_seq h riot_label_DeviceID) in
    let aliasKey_pub, aliasKey_priv = riot_derive_AliasKey_spec
                                        (B.as_seq h cdi)
                                        (B.as_seq h fwid)
                                        (B.len riot_label_AliasKey)
                                        (B.as_seq h riot_label_AliasKey) in
    let            aliasKey_crt_tbs = x509_get_aliasKey_crt_tbs_spec
                                        (B.as_seq h cdi)
                                        (B.as_seq h fwid)
                                        (riot_ver)
                                        (deviceID_pub)
                                        (aliasKey_pub)
                                        (aliasKey_crt_len)
                                        (aliasKey_crt_pos)
                                        (B.as_seq h aliasKey_crt) in
     (* `aliasKey_crt_tbs` has an Ed25519 signable length -- pre condition for `aliasKey_crt_pos` *)
     (* pre *) valid_ed25519_sign_mag_length (Seq.length aliasKey_crt_tbs) /\
    (let               aliasKey_crt = x509_get_aliasKey_crt_spec
                                        (deviceID_priv)
                                        (aliasKey_crt_tbs) in
     (* `aliasKey_crt` buffer has enough space *)
     (* pre *) Seq.length aliasKey_crt <= - v aliasKey_crt_pos )))
   (ensures fun h0 _ h1 -> True)
= ()

let () = ()

(*)
#restart-solver
#push-options "--query_stats --z3rlimit 256 --initial_fuel 8 --max_fuel 8 --initial_ifuel 4"
let riot_main
  (cdi : B.lbuffer uint8 32)
  (fwid: B.lbuffer uint8 32)
  (riot_ver: datatype_of_asn1_type INTEGER)
  (aliasKey_crt_len: size_t)
  (aliasKey_crt_pos: size_t)
  (aliasKey_crt: B.lbuffer pub_uint8 (v aliasKey_crt_len))
  (aliasKey_pub: B.lbuffer pub_uint8 32)
  (aliasKey_priv: B.lbuffer uint8 32)
: HST.Stack unit
  (requires fun h ->
    B.(all_live h [buf cdi;
                   buf fwid;
                   buf aliasKey_pub;
                   buf aliasKey_priv;
                   buf aliasKey_crt]) /\
    B.(all_disjoint [loc_buffer cdi;
                     loc_buffer fwid;
                     loc_buffer aliasKey_pub;
                     loc_buffer aliasKey_priv;
                     loc_buffer aliasKey_crt]) /\
    0 <= v aliasKey_crt_pos /\ v aliasKey_crt_pos <= v aliasKey_crt_len /\
    v aliasKey_crt_len + 64 <= max_size_t /\
   (let cdigest = Spec.Agile.Hash.hash alg (B.as_seq h cdi) in
    let deviceID_pub, deviceID_priv = riot_derive_key_pair_spec 32ul cdigest 2ul (B.as_seq h riot_label_DeviceID) in
    let adigest = Spec.Agile.HMAC.hmac alg cdigest (B.as_seq h fwid) in
    let aliasKey_pub, aliasKey_priv = riot_derive_key_pair_spec 32ul adigest 2ul (B.as_seq h riot_label_DeviceID) in
    let deviceID_pub32: B32.lbytes32 32ul = B32.hide deviceID_pub in
    let fwid32: B32.lbytes32 32ul = B32.hide (declassify_secret_bytes 32 (B.as_seq h fwid)) in
    let riot_extension = x509_get_riot_extension riot_ver deviceID_pub32 fwid32 in
    let riot_extension_sx = serialize_x509_extension_sequence_TLV serialize_compositeDeviceID_sequence_TLV
                            `serialize`
                            riot_extension in
    (* AliasKey Certificate TBS *)
    let aliasKey_crt_tbs = Seq.slice (B.as_seq h aliasKey_crt) 0 (v aliasKey_crt_pos)
                           `Seq.append` (* FIXME: Here, we need to require that `tbs`'s length is acceptable by the signing fun *)
                           riot_extension_sx in
    let _ = lemma_serialize_x509_extension_size serialize_compositeDeviceID_sequence_TLV riot_extension;
            (**) lemma_serialize_asn1_oid_TLV_size riot_extension.x509_extID;
            (**) lemma_serialize_asn1_boolean_TLV_size riot_extension.x509_extCritical;
            (**) lemma_serialize_compositeDeviceID_sequence_TLV_size_exact riot_extension.x509_extValue;
            lemma_serialize_x509_extension_sequence_TLV_size serialize_compositeDeviceID_sequence_TLV riot_extension in
    let aliasKey_crt_tbs = classify_public_bytes (Seq.length aliasKey_crt_tbs) aliasKey_crt_tbs in
    Seq.length aliasKey_crt_tbs + 64 <= max_size_t /\
   (let aliasKey_crt_sig = Spec.Ed25519.sign deviceID_priv aliasKey_crt_tbs in
    let aliasKey_crt_sig32: B32.lbytes32 64ul = B32.hide (declassify_secret_bytes 64 aliasKey_crt_sig) in
    let aliasKey_crt_sig_bs = {bs_len = 65ul; bs_unused_bits = 0ul; bs_s = aliasKey_crt_sig32} in
    (* AliasKey Certificate Signature *)
    // let aliasKey_crt_sig_sx = (OID_EC_ALG_UNRESTRICTED (*FIXME*) `serialize_envelop_OID_with` serialize_asn1_bit_string_TLV)
    //                           `serialize`
    //                           (lemma_serialize_asn1_bit_string_TLV_size aliasKey_crt_sig_bs;
    //                            (OID_EC_ALG_UNRESTRICTED, aliasKey_crt_sig_bs)) in
    v aliasKey_crt_len - v aliasKey_crt_pos >= 50)))
    // length_of_opaque_serialization serialize_compositeDeviceID_sequence_TLV (x509_get_compositeDeviceID) ))
  (ensures  fun h0 _ h1 ->
    True)
= admit() (*)
  HST.push_frame ();
  let cdi = HW.get_cdi st in
  let cDigest: b:B.buffer uint8{B.length b == v digest_len} = B.alloca (u8 0) digest_len in
  (**)assert_norm (v digest_len <= max_input_length alg);
  riot_hash alg
    cdi cdi_len    //in : data
    cDigest;       //out: digest
  let deviceID_private_key: b:B.buffer uint8{B.length b == v digest_len} = B.alloca (u8 0) digest_len in
  (**)assert_norm (v digest_len + block_length alg <= max_input_length alg);
  riot_derive_key_pair
    rout.deviceID_public_key //out: public key
    deviceID_private_key     //out: private key
    cDigest digest_len;      //in :ikm

  (* NOTE: Now I just fill the public key into the To-Be-Signed region *)
  B.blit
    rout.deviceID_public_key 0ul
    rout.deviceID_cert.tbs   0ul
    32ul;
  Ed25519.sign
    rout.deviceID_cert.sig  //out: signature
    deviceID_private_key    //in : secret
    32ul                    //in : msglen
    rout.deviceID_cert.tbs; //in : msg

  (* FIXME: just consider deviceID now *)
  // (* NOTE: hmac requires disjointness *)
  // let cfDigest: b:B.buffer uint8{B.length b == v digest_len} = B.alloca (u8 0) digest_len in
  // riot_hmac alg
  //   cfDigest            //out: tag
  //   cDigest digest_len  //in : key
  //   fwid    digest_len; //in : data
  // riot_derive_key_pair
  //   rout.alias_public_key  //out: public key
  //   rout.alias_private_key //out: private key
  //   cfDigest digest_len;   //in :ikm

  HST.pop_frame ()
