module X509.RIoT

module B32 = FStar.Bytes
(*)
open ASN1.Spec
open X509.Crypto
open X509.RIoT.Ext

open FStar.Integers

(* ZT: Some tests to indicate if the proof performance has been
       affected by some definitions from ASN1.* or Hacl.* *)
let _ = assert (length_of_oid OID_EC_GRP_SECP256R1 == 6)
let _ = assert (length_of_asn1_primitive_TLV (Mkbit_string_t 33ul 0ul (magic())) == 35)

#restart-solver
#push-options "--query_stats --z3rlimit 32 --initial_fuel 8 --initial_ifuel 2"
let x509GetRIoTExtension
  (version: datatype_of_asn1_type INTEGER)
  (deviceKeyPub: B32.lbytes32 32ul)
  (fwid_len: asn1_value_int32_of_type OCTET_STRING {v fwid_len <= asn1_length_max - 106})
  (fwid: B32.lbytes32 fwid_len)
: Tot (riot_extension_t_inbound)
=
  let deviceKeyPub_bs: datatype_of_asn1_type BIT_STRING = Mkbit_string_t 33ul 0ul deviceKeyPub in
  let alg_id: algorithmIdentifier_ECDSA_P256_t = {  // 1 + 1 + (7 + 8) = 17
     alg_id_oid_ecdsa = OID_EC_ALG_UNRESTRICTED;    // 1 + 1 + 5 = 7
     alg_id_oid_p256  = OID_EC_GRP_SECP256R1        // 1 + 1 + 6 = 8
  } in
  (* Prf *) lemma_serialize_algorithmIdentifier_sequence_ECDSA_P256_unfold alg_id;
  (* Prf *) lemma_serialize_asn1_oid_TLV_size alg_id.alg_id_oid_ecdsa;
  (* Prf *) lemma_serialize_asn1_oid_TLV_size alg_id.alg_id_oid_p256;
  (* Prf *) lemma_serialize_algorithmIdentifier_sequence_TLV_ECDSA_P256_size alg_id;

  let deviceIDPublicKeyInfo: subjectPublicKeyInfo_ECDSA_P256_t = // 1 + 1 + (17 + 35) = 54
      { subjectPubKey_alg = alg_id;                             // 17
        subjectPubKey     = deviceKeyPub_bs } in                // 1 + 1 + 33 = 35
  (* Prf *) lemma_serialize_subjectPublicKeyInfo_sequence_ECDSA_P256_unfold deviceIDPublicKeyInfo;
  (* Prf *) lemma_serialize_subjectPublicKeyInfo_sequence_ECDSA_P256_size deviceIDPublicKeyInfo;
  (* Prf *) lemma_serialize_asn1_bit_string_TLV_size deviceIDPublicKeyInfo.subjectPubKey;
  (* Prf *) lemma_serialize_subjectPublicKeyInfo_sequence_TLV_ECDSA_P256_size deviceIDPublicKeyInfo;

  let fwid: fwid_t =                       // <= 1 + 5 + (11 + 6 + fwid_len) = 23 + fwid_len
  { fwid_hashAlg = OID_DIGEST_SHA256;      // 1 + 1 + 9 = 11
    fwid_value   = (|fwid_len, fwid|) } in // <= 1 + 5 + fwid_len = 6 + fwid_len
  (* Prf *) lemma_serialize_fwid_sequence_size fwid;
  (* Prf *) assert (asn1_value_length_inbound_of_type SEQUENCE
                     (length_of_asn1_primitive_TLV fwid.fwid_hashAlg +
                      length_of_asn1_primitive_TLV fwid.fwid_value));
  (* Prf *) lemma_serialize_fwid_sequence_TLV_size fwid;

  let compositeDeviceID: compositeDeviceID_t = { // <= 1 + 5 + (6 + 54 + 23 + fwid_len) = 89 + fwid_len
    device_version  = version;                   // <= 1 + 1 + 4 = 6 (* FIXME *)
    deviceID        = deviceIDPublicKeyInfo;      // 54
    fwid            = fwid                       // <= 23 + fwid_len
  } in
  (* Prf *) lemma_serialize_compositeDeviceID_sequence_size compositeDeviceID;
  (* Prf *) lemma_serialize_asn1_integer_TLV_size compositeDeviceID.device_version;
  (* Prf *) lemma_serialize_compositeDeviceID_sequence_TLV_size compositeDeviceID;

  let riot_extension: riot_extension_t = {     // <= 1 + 5 + (11 + 89 + fwid_len) = 106 + fwid_len
    riot_oid               = OID_RIOT;         // 1 + 1 + 9 = 11
    riot_compositeDeviceID = compositeDeviceID // <= 89 + fwid_len
  } in
  (* Prf *) lemma_serialize_riot_extension_sequence_unfold riot_extension;
  (* Prf *) lemma_serialize_asn1_oid_TLV_size riot_extension.riot_oid;
  (* Prf *) lemma_serialize_riot_extension_sequence_TLV_size riot_extension;

(* return *) riot_extension
#pop-options

#push-options "--query_stats --z3rlimit 16 --initial_fuel 2 --initial_ifuel 1"
let x509GetAliasKeyInfo
  (aliasKeyPub: B32.lbytes32 32ul)
= let aliasKeyPub_bs: datatype_of_asn1_type BIT_STRING = Mkbit_string_t 33ul 0ul aliasKeyPub in
  let alg_id: algorithmIdentifier_ECDSA_P256_t = {  // 1 + 1 + (7 + 8) = 17
     alg_id_oid_ecdsa = OID_EC_ALG_UNRESTRICTED;    // 1 + 1 + 5 = 7
     alg_id_oid_p256  = OID_EC_GRP_SECP256R1        // 1 + 1 + 6 = 8
  } in
  (* Prf *) lemma_serialize_algorithmIdentifier_sequence_ECDSA_P256_unfold alg_id;
  (* Prf *) lemma_serialize_asn1_oid_TLV_size alg_id.alg_id_oid_ecdsa;
  (* Prf *) lemma_serialize_asn1_oid_TLV_size alg_id.alg_id_oid_p256;
  (* Prf *) lemma_serialize_algorithmIdentifier_sequence_TLV_ECDSA_P256_size alg_id;

  let aliasPublicKeyInfo: subjectPublicKeyInfo_ECDSA_P256_t = // 1 + 1 + (17 + 35) = 54
      { subjectPubKey_alg = alg_id;                             // 17
        subjectPubKey     = aliasKeyPub_bs } in                // 1 + 1 + 33 = 35
  (* Prf *) lemma_serialize_subjectPublicKeyInfo_sequence_ECDSA_P256_unfold aliasPublicKeyInfo;
  (* Prf *) lemma_serialize_subjectPublicKeyInfo_sequence_ECDSA_P256_size aliasPublicKeyInfo;
  (* Prf *) lemma_serialize_asn1_bit_string_TLV_size aliasPublicKeyInfo.subjectPubKey;
  (* Prf *) lemma_serialize_subjectPublicKeyInfo_sequence_TLV_ECDSA_P256_size aliasPublicKeyInfo;

(* return *) aliasPublicKeyInfo
#pop-options
