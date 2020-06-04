module RIoT.X509

module B32 = FStar.Bytes

open ASN1.Spec
open X509
include RIoT.X509.Base
include RIoT.X509.FWID
include RIoT.X509.CompositeDeviceID
open FStar.Integers

(* ZT: Some tests to indicate if the proof performance has been
       affected by some definitions from ASN1.* or Hacl.* *)
let _ = assert (length_of_oid OID_EC_GRP_SECP256R1 == 6)
let _ = assert (length_of_asn1_primitive_TLV (Mkbit_string_t 33ul 0ul (magic())) == 35)

#push-options "--query_stats --z3rlimit 16 --initial_fuel 2 --initial_ifuel 1"
let x509_get_public_key_info
  (pubkey_alg: cryptoAlg)
  (pubkey: pubkey_t pubkey_alg)
: Tot (subjectPublicKeyInfo_t_inbound pubkey_alg)
= let pubkey_bs: datatype_of_asn1_type BIT_STRING = Mkbit_string_t 33ul 0ul pubkey in
  if (pubkey_alg = ECDSA_P256) then
  ( let alg_id: algorithmIdentifier_t pubkey_alg = {  // 1 + 1 + (7 + 8) = 17
       alg_id_oid_ecdsa = OID_EC_ALG_UNRESTRICTED;    // 1 + 1 + 5 = 7
       alg_id_oid_p256  = OID_EC_GRP_SECP256R1        // 1 + 1 + 6 = 8
    } in
    (* Prf *) lemma_serialize_algorithmIdentifier_unfold pubkey_alg alg_id;
    (* Prf *) lemma_serialize_asn1_oid_TLV_size alg_id.alg_id_oid_ecdsa;
    (* Prf *) lemma_serialize_asn1_oid_TLV_size alg_id.alg_id_oid_p256;
    (* Prf *) lemma_serialize_algorithmIdentifier_sequence_TLV_size pubkey_alg alg_id;

    let aliasPublicKeyInfo: subjectPublicKeyInfo_t pubkey_alg = {// 1 + 1 + (17 + 35) = 54
       subjectPubKey_alg = alg_id;                             // 17
       subjectPubKey     = pubkey_bs
    } in                // 1 + 1 + 33 = 35
  (* Prf *) lemma_serialize_subjectPublicKeyInfo_unfold pubkey_alg aliasPublicKeyInfo;
  (* Prf *) lemma_serialize_subjectPublicKeyInfo_size pubkey_alg aliasPublicKeyInfo;
  (* Prf *) lemma_serialize_asn1_bit_string_TLV_size aliasPublicKeyInfo.subjectPubKey;
  (* Prf *) lemma_serialize_subjectPublicKeyInfo_sequence_TLV_size pubkey_alg aliasPublicKeyInfo;

  (* return *) aliasPublicKeyInfo )
  else
  ( false_elim() )
#pop-options

#push-options "--query_stats --z3rlimit 96 --initial_fuel 16 --max_fuel 32 --initial_ifuel 2"
let x509_get_compositeDeviceID
  (version: datatype_of_asn1_type INTEGER)
  (deviceKeyPub: B32.lbytes32 32ul)
  (fwid: B32.lbytes32 32ul)
: Tot (compositeDeviceID_t_inbound)
= let deviceIDPublicKeyInfo: subjectPublicKeyInfo_t alg_DeviceID = x509_get_public_key_info alg_DeviceID deviceKeyPub in
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

(*return*) compositeDeviceID
#pop-options

(* TODO)
let _ = assert (length_of_oid OID_EC_GRP_SECP256R1 == 6)
let _ = assert (length_of_asn1_primitive_TLV (Mkbit_string_t 33ul 0ul (magic())) == 35)

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
