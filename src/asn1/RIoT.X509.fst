module RIoT.X509

module B32 = FStar.Bytes

open ASN1.Spec
open X509
include RIoT.X509.Base
include RIoT.X509.FWID
include RIoT.X509.CompositeDeviceID
include RIoT.X509.Extension
include RIoT.X509.AliasKeyTBS
include RIoT.X509.AliasKeyCRT
open FStar.Integers

(* ZT: Some tests to indicate if the proof performance has been
       affected by some definitions from ASN1.* or Hacl.* *)
#set-options "--z3rlimit 16"
let _ = assert (length_of_oid OID_EC_GRP_SECP256R1 == 6)
let _ = assert (length_of_asn1_primitive_value (Mkbit_string_t 33ul 0ul (magic())) == 33)

open X509.Base
open ASN1.Spec.Base

open Lib.IntTypes
open RIoT.Base
open RIoT.Declassify
open Spec.Hash.Definitions

module B = LowStar.Buffer
module IB = LowStar.ImmutableBuffer
module HS  = FStar.HyperStack
module HST = FStar.HyperStack.ST

let bytes_pub  = Seq.seq pub_uint8
let lbytes_pub = Seq.lseq pub_uint8
let bytes_sec  = Seq.seq uint8
let lbytes_sec = Seq.lseq uint8

#restart-solver
#push-options "--query_stats --z3rlimit 64 --initial_fuel 2 --initial_ifuel 2"
let x509_get_aliasKey_crt_tbs_spec
  (fwid: lbytes_sec 32)
  (riot_ver: datatype_of_asn1_type INTEGER)
  (deviceID_pub: lbytes_pub 32)
  (aliasKey_pub: lbytes_pub 32)
  (aliasKey_crt_len: size_t)
  (aliasKey_crt_pos: size_t { 0 <= v aliasKey_crt_pos /\
                              v aliasKey_crt_pos <= v aliasKey_crt_len })
  (aliasKey_crt: lbytes_pub (v aliasKey_crt_len))
: GTot (s: bytes_pub { Seq.length s == v aliasKey_crt_pos + length_of_asn1_primitive_TLV riot_ver + 155 /\
                       Seq.length s <= v aliasKey_crt_pos + 161 })
=
  (* RIoT Extension *)
  (*   Wrap `bytes` to `B32.bytes` *)
  let deviceID_pub32: B32.lbytes32 32ul = B32.hide deviceID_pub in
  let fwid32        : B32.lbytes32 32ul = B32.hide (declassify_secret_bytes fwid) in
  (*   Construct `riot_extension` to serialize *)
  let riot_extension    = x509_get_riot_extension riot_ver fwid32 deviceID_pub32 in
  (*   Get serialization of `riot_extension` *)
  let riot_extension_sx = serialize_riot_extension_sequence_TLV `serialize` riot_extension in
  (* Prf *) lemma_serialize_riot_extension_sequence_TLV_size_exact riot_extension;

  (* AliasKey SubjectPublicKeyInfo *)
  (*   Wrap `bytes` to `B32.bytes` *)
  let aliasKey_pub32: B32.lbytes32 32ul = B32.hide aliasKey_pub in
  let aliasKey_pub_info    = x509_get_subjectPublicKeyInfo alg_AliasKey aliasKey_pub32 in
  let aliasKey_pub_info_sx = serialize_subjectPublicKeyInfo_sequence_TLV alg_AliasKey `serialize` aliasKey_pub_info in
  (* Prf *) lemma_serialize_subjectPublicKeyInfo_sequence_TLV_size_exact alg_AliasKey aliasKey_pub_info;

  (* AliasKey Certificate TBS *)
  let aliasKey_crt_tbs = Seq.slice aliasKey_crt 0 (v aliasKey_crt_pos)
                         `Seq.append`
                         aliasKey_pub_info_sx
                         `Seq.append`
                         riot_extension_sx in

(* return *) aliasKey_crt_tbs
#pop-options


let valid_ed25519_sign_mag_length
  (l: nat)
= 64 + l <= max_size_t

#push-options "--query_stats --z3rlimit 64 --fuel 4 --ifuel 4"
let x509_get_aliasKey_crt_tbs
  (fwid: B.lbuffer uint8 32)
  (riot_ver: datatype_of_asn1_type INTEGER)
  (deviceID_pub: B.lbuffer pub_uint8 32)
  (aliasKey_pub: B.lbuffer pub_uint8 32)
  (aliasKey_crt_len: size_t)
  (aliasKey_crt_pos: size_t { 0 <= v aliasKey_crt_pos /\
                              v aliasKey_crt_pos <= v aliasKey_crt_len })
  (aliasKey_crt: B.lbuffer pub_uint8 (v aliasKey_crt_len))
: HST.Stack unit
  (requires fun h ->
    B.(all_live h [buf fwid;
                   buf deviceID_pub;
                   buf aliasKey_pub;
                   buf aliasKey_crt]) /\
    B.(all_disjoint [loc_buffer fwid;
                     loc_buffer deviceID_pub;
                     loc_buffer aliasKey_pub;
                     loc_buffer aliasKey_crt]) /\
    (* pre *) 0 <= v aliasKey_crt_pos /\ v aliasKey_crt_pos <= v aliasKey_crt_len /\
    (* pre: buffer has enough space *)
   (let            aliasKey_crt_tbs = x509_get_aliasKey_crt_tbs_spec
                                        (B.as_seq h fwid)
                                        (riot_ver)
                                        (B.as_seq h deviceID_pub)
                                        (B.as_seq h aliasKey_pub)
                                        (aliasKey_crt_len)
                                        (aliasKey_crt_pos)
                                        (B.as_seq h aliasKey_crt) in
     (* pre *) Seq.length (aliasKey_crt_tbs) <= v aliasKey_crt_len)
   )
  (ensures fun h0 _ h1 ->
    True
  )
=
  HST.push_frame ();

  (* RIoT Extension *)
  (*   Wrap `bytes` to `B32.bytes` *)
  let deviceID_pub32: B32.lbytes32 32ul = B32.of_buffer 32ul deviceID_pub in
  let fwid_pub      : B.lbuffer pub_uint8 32 = B.alloca 0x00uy 32ul in
  declassify_secret_buffer 32ul fwid fwid_pub;
  let fwid_pub32        : B32.lbytes32 32ul = B32.of_buffer 32ul fwid_pub in
  (*   Construct `riot_extension` to serialize *)
  let riot_extension    = x509_get_riot_extension riot_ver deviceID_pub32 fwid_pub32 in

  let offset = serialize32_riot_extension_sequence_TLV_backwards
                 riot_extension
                 aliasKey_crt
                 aliasKey_crt_len in

  let aliasKey_pub32: B32.lbytes32 32ul = B32.of_buffer 32ul aliasKey_pub in
  let aliasKey_pub_info    = x509_get_subjectPublicKeyInfo alg_AliasKey aliasKey_pub32 in

  let offset = serialize32_subjectPublicKeyInfo_sequence_TLV_backwards

                 aliasKey_pub_info
                 aliasKey_crt
                 (aliasKey_crt_len - offset) in

  HST.pop_frame ()
#pop-options


#push-options "--z3rlimit 16 --fuel 2 --ifuel 2"
let x509_get_aliasKey_crt_tbs_sig_sx_spec
  (deviceID_priv: lbytes_sec 32)
  (aliasKey_crt_tbs: bytes_pub {64 + Seq.length aliasKey_crt_tbs <= max_size_t})
: GTot (lbytes_pub 69)
=
  let aliasKey_crt_tbs_sec = classify_public_bytes aliasKey_crt_tbs in
  let aliasKey_crt_tbs_sig = Spec.Ed25519.sign deviceID_priv aliasKey_crt_tbs_sec in
  let aliasKey_crt_tbs_sig32 = B32.hide (declassify_secret_bytes aliasKey_crt_tbs_sig) in
  let aliasKey_crt_tbs_sig_bs = x509_get_signature ED25519 aliasKey_crt_tbs_sig32 in
  let aliasKey_crt_tbs_sig_sx = serialize_x509_signature_sequence_TLV ED25519
                                `serialize`
                                aliasKey_crt_tbs_sig_bs in
  (* Prf *) lemma_serialize_x509_signature_sequence_TLV_size_exact ED25519 aliasKey_crt_tbs_sig_bs;

(* return *) aliasKey_crt_tbs_sig_sx
#pop-options

#push-options "--z3rlimit 32 --initial_fuel 2 --initial_ifuel 2"
let x509_get_aliasKey_crt_spec
  (deviceID_priv: lbytes_sec 32)
  (aliasKey_crt_tbs: bytes_pub {64 + Seq.length aliasKey_crt_tbs <= max_size_t})
: GTot (aliasKey_crt: bytes_pub { Seq.length aliasKey_crt == Seq.length aliasKey_crt_tbs + 76 })
=
  let aliasKey_crt_tbs_sig_sx = x509_get_aliasKey_crt_tbs_sig_sx_spec
                                  deviceID_priv
                                  aliasKey_crt_tbs in
  let aliasKey_crt_tbs_sig_algId = x509_get_algorithmIdentifier ED25519 in
  let aliasKey_crt_tbs_sig_algId_sx = serialize_algorithmIdentifier_sequence_TLV ED25519
                                      `serialize`
                                      aliasKey_crt_tbs_sig_algId in
  (* Prf *) lemma_serialize_algorithmIdentifier_sequence_TLV_size_exact ED25519 aliasKey_crt_tbs_sig_algId;

  let aliasKey_crt = aliasKey_crt_tbs
                     `Seq.append`
                     aliasKey_crt_tbs_sig_algId_sx
                     `Seq.append`
                     aliasKey_crt_tbs_sig_sx in

  // assert ( Seq.length aliasKey_crt ==
  //          Seq.length aliasKey_crt_tbs +
  //          Seq.length aliasKey_crt_tbs_sig_algId_sx +
  //          Seq.length aliasKey_crt_tbs_sig_sx );

(* return *) aliasKey_crt
#pop-options

(*)
#restart-solver
#push-options "--query_stats --z3rlimit 128 --fuel 16 --ifuel 4"
let x509_get_riot_extension
  (version: datatype_of_asn1_type INTEGER)
  (deviceKeyPub: B32.lbytes32 32ul)
  (fwid: B32.lbytes32 32ul)
: Tot (x509_extension_t_inbound serialize_compositeDeviceID_sequence_TLV)
=
  let compositeDeviceID: compositeDeviceID_t_inbound = x509_get_compositeDeviceID version deviceKeyPub fwid in
  (* Prf *) lemma_serialize_compositeDeviceID_sequence_TLV_size_exact compositeDeviceID;

  let riot_extension: x509_extension_t serialize_compositeDeviceID_sequence_TLV = {
    x509_extID       = OID_RIOT;
    x509_extCritical = false;
    x509_extValue    = compositeDeviceID
  } in
  (* Prf *) lemma_serialize_x509_extension_unfold
            (* s *) serialize_compositeDeviceID_sequence_TLV
            (* x *) riot_extension;
  (* Prf *) lemma_serialize_x509_extension_size
            (* s *) serialize_compositeDeviceID_sequence_TLV
            (* x *) riot_extension;
  (* Prf *) (**) lemma_serialize_asn1_oid_TLV_size riot_extension.x509_extID;
  (* Prf *) (**) lemma_serialize_asn1_boolean_TLV_size riot_extension.x509_extCritical;
  // assume (length_of_asn1_primitive_TLV riot_extension.x509_extID == 11); ()
  // assume (length_of_asn1_primitive_TLV riot_extension.x509_extCritical == 3);
  // assert_norm (length_of_asn1_primitive_TLV riot_extension.x509_extValue.riot_version <= 6);
  // assert_norm (length_of_opaque_serialization serialize_fwid_sequence_TLV riot_extension.x509_extValue.riot_fwid == 47);
  // (* Prf *) lemma_serialize_x509_extension_sequence_TLV_size
  //           (* s *) serialize_compositeDeviceID_sequence_TLV
  //           (* x *) riot_extension;

(*return*) riot_extension
#pop-options


#push-options "--query_stats --z3rlimit 32 --fuel 8 --ifuel 4"
let lemma_serialize_riot_extension_oid
  (x: x509_extension_t serialize_compositeDeviceID_sequence_TLV)
: Lemma (
  // length_of_asn1_primitive_TLV x.x509_extID == 11
  x.x509_extID == OID_RIOT
)
= ()

let lemma_serialize_riot_extension_size_exact
  (x: x509_extension_t serialize_compositeDeviceID_sequence_TLV)
: Lemma (
  length_of_opaque_serialization (serialize_x509_extension serialize_compositeDeviceID_sequence_TLV) x ==
  length_of_asn1_primitive_TLV x.x509_extValue.riot_version + 109 // (93 +1+1) + 11 + 3 +1+1
)
= //lemma_serialize_x509_extension_sequence_TLV_size serialize_compositeDeviceID_sequence_TLV x;
  lemma_serialize_x509_extension_size              serialize_compositeDeviceID_sequence_TLV x;
  assert (length_of_opaque_serialization (serialize_x509_extension serialize_compositeDeviceID_sequence_TLV) x ==
          length_of_asn1_primitive_TLV x.x509_extID +
          length_of_asn1_primitive_TLV x.x509_extCritical +
          length_of_TLV OCTET_STRING (length_of_opaque_serialization serialize_compositeDeviceID_sequence_TLV x.x509_extValue));
  (**) lemma_serialize_asn1_oid_TLV_size                         x.x509_extID;
  // (**) lemma_serialize_asn1_boolean_TLV_size                     x.x509_extCritical;
  // (**) lemma_serialize_compositeDeviceID_sequence_TLV_size_exact x.x509_extValue;
  assert (length_of_asn1_primitive_TLV x.x509_extID == 11);
  admit();
()
#pop-options

open Lib.IntTypes
open RIoT.Base
open RIoT.Declassify
open Spec.Hash.Definitions

let bytes_pub  = Seq.seq pub_uint8
let lbytes_pub = Seq.lseq pub_uint8
let bytes_sec  = Seq.seq uint8
let lbytes_sec = Seq.lseq uint8


#restart-solver
#push-options "--query_stats --z3rlimit 256 --initial_fuel 8 --initial_ifuel 3"
let x509_get_aliasKey_crt_tbs_spec
  (cdi: lbytes_sec 32)
  (fwid: lbytes_sec 32)
  (riot_ver: datatype_of_asn1_type INTEGER)
  (riot_label_DeviceID_len: size_t { (* for Hacl.HKDF.expand_st *)
                                     hash_length alg + v riot_label_DeviceID_len + 1 + block_length alg < pow2 32 /\
                                     (* for Spec.Aigle.HKDF.expand *)
                                     hash_length alg + v riot_label_DeviceID_len + 1 + block_length alg < max_input_length alg })
  (riot_label_DeviceID: lbytes_sec (v riot_label_DeviceID_len))
  (aliasKey_crt_len: size_t)
  (aliasKey_crt_pos: size_t { 0 <= v aliasKey_crt_pos /\
                              v aliasKey_crt_pos <= v aliasKey_crt_len })
  (aliasKey_crt: lbytes_pub (v aliasKey_crt_len))
// : GTot (l: nat & lbytes_pub l)
= let cdigest = Spec.Agile.Hash.hash alg cdi in
  let deviceID_pub, deviceID_priv = riot_derive_key_pair_spec
                                    (* ikm *) 32ul cdigest
                                    (* lbl *) riot_label_DeviceID_len riot_label_DeviceID in
  let adigest = Spec.Agile.HMAC.hmac alg cdigest fwid in
  let aliasKey_pub, aliasKey_priv = riot_derive_key_pair_spec
                                    (* ikm *) 32ul adigest
                                    (* lbl *) riot_label_DeviceID_len riot_label_DeviceID in
  let deviceID_pub32: B32.lbytes32 32ul = B32.hide deviceID_pub in
  let fwid32: B32.lbytes32 32ul = B32.hide (declassify_secret_bytes 32 fwid) in
  let riot_extension = x509_get_riot_extension riot_ver deviceID_pub32 fwid32 in
  let riot_extension_sx = serialize_x509_extension_sequence_TLV serialize_compositeDeviceID_sequence_TLV
                          `serialize`
                          riot_extension in
  (* AliasKey Certificate TBS *)
  let aliasKey_crt_tbs = Seq.slice aliasKey_crt 0 (v aliasKey_crt_pos)
                         `Seq.append` (* FIXME: Here, we need to require that `tbs`'s length is acceptable by the signing func *)
                         riot_extension_sx in
  // let _ = lemma_serialize_x509_extension_size serialize_compositeDeviceID_sequence_TLV riot_extension;
  //         (**) lemma_serialize_asn1_oid_TLV_size riot_extension.x509_extID;
  //         (**) lemma_serialize_asn1_boolean_TLV_size riot_extension.x509_extCritical;
  //         (**) lemma_serialize_compositeDeviceID_sequence_TLV_size_exact riot_extension.x509_extValue;
  //         lemma_serialize_x509_extension_sequence_TLV_size serialize_compositeDeviceID_sequence_TLV riot_extension in
  // let aliasKey_crt_tbs = classify_public_bytes (Seq.length aliasKey_crt_tbs) aliasKey_crt_tbs in

(* return *) (|Seq.length aliasKey_crt_tbs, aliasKey_crt_tbs|)

// let _ = assert (length_of_oid OID_EC_GRP_SECP256R1 == 6)
// let _ = assert (length_of_asn1_primitive_TLV (Mkbit_string_t 33ul 0ul (magic())) == 35)

(*
#push-options "--query_stats --z3rlimit 96 --initial_fuel 16 --max_fuel 32 --initial_ifuel 2"
let x509_get_riot_extension
  (version: datatype_of_asn1_type INTEGER)
  (deviceKeyPub: B32.lbytes32 32ul)
  (fwid: B32.lbytes32 32ul)
: Tot (x509_extension_t_inbound serialize_compositeDeviceID_sequence_TLV)
=
  // lemma_serialize_asn1_oid_TLV_size OID_RIOT;
  // assert (length_of_opaque_serialization serialize_asn1_oid_TLV OID_RIOT == 11);
  // (* Prf *) (**) lemma_serialize_asn1_boolean_TLV_size false;
  // assert (length_of_opaque_serialization serialize_asn1_boolean_TLV false == 3);
  let deviceIDPublicKeyInfo: subjectPublicKeyInfo_t alg_DeviceID = x509_get_public_key_info alg_DeviceID deviceKeyPub in
  (* Prf *) lemma_serialize_subjectPublicKeyInfo_unfold alg_DeviceID deviceIDPublicKeyInfo;
  (* Prf *) lemma_serialize_subjectPublicKeyInfo_size alg_DeviceID deviceIDPublicKeyInfo;
  (* Prf *)      lemma_serialize_algorithmIdentifier_unfold alg_DeviceID deviceIDPublicKeyInfo.subjectPubKey_alg;
  (* Prf *)      (**) lemma_serialize_asn1_oid_TLV_size deviceIDPublicKeyInfo.subjectPubKey_alg.alg_id_oid_ecdsa;
  (* Prf *)      (**) lemma_serialize_asn1_oid_TLV_size deviceIDPublicKeyInfo.subjectPubKey_alg.alg_id_oid_p256;
  (* Prf *)      lemma_serialize_algorithmIdentifier_sequence_TLV_size alg_DeviceID deviceIDPublicKeyInfo.subjectPubKey_alg;
  (* Prf *) (**) lemma_serialize_asn1_bit_string_TLV_size deviceIDPublicKeyInfo.subjectPubKey;
  (* Prf *) lemma_serialize_subjectPublicKeyInfo_sequence_TLV_size alg_DeviceID deviceIDPublicKeyInfo;

  let fwid: fwid_t = {
    fwid_hashAlg = OID_DIGEST_SHA256;
    fwid_value   = (|32ul, fwid|)
  } in
  (* Prf *) lemma_serialize_fwid_size fwid;
  (* Prf *) (**) lemma_serialize_asn1_oid_TLV_size fwid.fwid_hashAlg;
  (* Prf *) (**) lemma_serialize_asn1_octet_string_TLV_size fwid.fwid_value;
  (* Prf *) lemma_serialize_fwid_sequence_TLV_size fwid;

  let compositeDeviceID: compositeDeviceID_t = {
    riot_version  = version;
    riot_deviceID = deviceIDPublicKeyInfo;
    riot_fwid     = fwid
  } in
  (* Prf *) lemma_serialize_compositeDeviceID_size compositeDeviceID;
  (* Prf *) (**) lemma_serialize_asn1_integer_TLV_size compositeDeviceID.riot_version;
  (* Prf *) lemma_serialize_compositeDeviceID_sequence_TLV_size compositeDeviceID;

  let riot_extension: x509_extension_t serialize_compositeDeviceID_sequence_TLV = {
    x509_extID       = OID_RIOT;
    x509_extCritical = false;
    x509_extValue    = compositeDeviceID
  } in
  (* Prf *) lemma_serialize_x509_extension_unfold
            (* s *) serialize_compositeDeviceID_sequence_TLV
            (* x *) riot_extension;
  (* Prf *) lemma_serialize_x509_extension_size
            (* s *) serialize_compositeDeviceID_sequence_TLV
            (* x *) riot_extension;
  (* Prf *) (**) lemma_serialize_asn1_oid_TLV_size riot_extension.x509_extID;
  (* Prf *) (**) lemma_serialize_asn1_boolean_TLV_size riot_extension.x509_extCritical;
  (* FIXME: ZT: They are true, but Z3 has trouble to prove them in a not small query. *)
  assume (length_of_opaque_serialization serialize_asn1_oid_TLV riot_extension.x509_extID == 11);
  assume (length_of_opaque_serialization serialize_asn1_boolean_TLV riot_extension.x509_extCritical == 3);
  assume (length_of_opaque_serialization (serialize_x509_extension serialize_compositeDeviceID_sequence_TLV) riot_extension
          <= asn1_length_max - 6);
  (* Prf *) lemma_serialize_x509_extension_sequence_TLV_size
            (* s *) serialize_compositeDeviceID_sequence_TLV
            (* x *) riot_extension;
(*return*) riot_extension
#pop-options

let _ = assert (length_of_oid OID_EC_GRP_SECP256R1 == 6)
let _ = assert (length_of_asn1_primitive_TLV (Mkbit_string_t 33ul 0ul (magic())) == 35)

(*)
#restart-solver
#push-options "--query_stats --z3rlimit 96 --initial_fuel 8 --initial_ifuel 2"// --initial_fuel 8 --max_fuel 16 --initial_ifuel 2"// 96 --max_fuel 16 --max_ifuel 16"
let x509_get_riot_extension
  (version: datatype_of_asn1_type INTEGER)
  (deviceKeyPub: B32.lbytes32 32ul)
  (fwid: B32.lbytes32 32ul)
// : Tot (x509_extension_t_inbound serialize_compositeDeviceID_sequence_TLV)
=
  let compositeDeviceID = x509_get_compositeDeviceID
                            version
                            deviceKeyPub
                            fwid in
  (* Prf *) lemma_serialize_compositeDeviceID_unfold compositeDeviceID;
  (* Prf *) lemma_serialize_compositeDeviceID_size   compositeDeviceID;
                 (* version *)
  (* Prf *) (**) lemma_serialize_asn1_integer_TLV_size compositeDeviceID.riot_version;
  (* Prf *)      lemma_serialize_subjectPublicKeyInfo_unfold alg_DeviceID compositeDeviceID.riot_deviceID;
  (* Prf *)      lemma_serialize_subjectPublicKeyInfo_size   alg_DeviceID compositeDeviceID.riot_deviceID;
  (* Prf *)           lemma_serialize_algorithmIdentifier_unfold alg_DeviceID compositeDeviceID.riot_deviceID.subjectPubKey_alg;
  (* Prf *)           lemma_serialize_algorithmIdentifier_size   alg_DeviceID compositeDeviceID.riot_deviceID.subjectPubKey_alg;
  (* Prf *)           (**) lemma_serialize_asn1_oid_TLV_size compositeDeviceID.riot_deviceID.subjectPubKey_alg.alg_id_oid_ecdsa;
  (* Prf *)           (**) lemma_serialize_asn1_oid_TLV_size compositeDeviceID.riot_deviceID.subjectPubKey_alg.alg_id_oid_p256;
  (* Prf *)           lemma_serialize_algorithmIdentifier_sequence_TLV_size alg_DeviceID compositeDeviceID.riot_deviceID.subjectPubKey_alg;
  (* Prf *)      (**) lemma_serialize_asn1_bit_string_TLV_size compositeDeviceID.riot_deviceID.subjectPubKey;
  (* Prf *)      lemma_serialize_subjectPublicKeyInfo_sequence_TLV_unfold alg_DeviceID compositeDeviceID.riot_deviceID;
                 (* fwid *)
  (* Prf *)      lemma_serialize_fwid_unfold compositeDeviceID.riot_fwid;
  (* Prf *)      lemma_serialize_fwid_size   compositeDeviceID.riot_fwid;
  (* Prf *)      (**) lemma_serialize_asn1_oid_TLV_size compositeDeviceID.riot_fwid.fwid_hashAlg;
  (* Prf *)      (**) lemma_serialize_asn1_octet_string_TLV_size compositeDeviceID.riot_fwid.fwid_value;
  (* Prf *)      lemma_serialize_fwid_sequence_TLV_size compositeDeviceID.riot_fwid;
  (* Prf *) lemma_serialize_compositeDeviceID_sequence_TLV_unfold compositeDeviceID;
  (* Prf *) lemma_serialize_compositeDeviceID_sequence_TLV_size   compositeDeviceID; admit();
  assert (length_of_opaque_serialization serialize_compositeDeviceID_sequence_TLV compositeDeviceID
          == length_of_asn1_envelop_tag_with_TLV SEQUENCE serialize_compositeDeviceID compositeDeviceID)
  // assert (length_of_opaque_serialization serialize_compositeDeviceID compositeDeviceID <= asn1_length_max - 6);
  // assert (length_of_opaque_serialization serialize_compositeDeviceID_sequence_TLV compositeDeviceID <= asn1_length_max - 6)
  // assert (let l = length_of_opaque_serialization serialize_compositeDeviceID compositeDeviceID in
  //         length_of_opaque_serialization serialize_compositeDeviceID_sequence_TLV compositeDeviceID ==
  //         1 + length_of_asn1_length (u l) + l)

  let riot_extension: x509_extension_t serialize_compositeDeviceID_sequence_TLV = {
    x509_extID       = OID_RIOT;
    x509_extCritical = false;
    x509_extValue    = compositeDeviceID
  } in
  (* Prf *) lemma_serialize_x509_extension_unfold
            (* s *) serialize_compositeDeviceID_sequence_TLV
            (* x *) riot_extension;
  (* Prf *) lemma_serialize_x509_extension_size
            (* s *) serialize_compositeDeviceID_sequence_TLV
            (* x *) riot_extension;
  (* Prf *) (**) lemma_serialize_asn1_oid_TLV_size riot_extension.x509_extID;
  (* Prf *) (**) lemma_serialize_asn1_boolean_TLV_size riot_extension.x509_extCritical;
  (* Prf *) lemma_serialize_x509_extension_sequence_TLV_size
            (* s *) serialize_compositeDeviceID_sequence_TLV
            (* x *) riot_extension;
(* return *) riot_extension
