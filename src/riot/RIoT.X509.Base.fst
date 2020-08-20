module RIoT.X509.Base
open X509.Base
open X509.ExtFields.KeyUsage

let aliasKeyCrt_key_usage: key_usage_payload_t
= x509_KU_KEY_CERT_SIGN
  (*
   * Adding more key usage bits for test only. According to the
   * [reference implementation](https://github.com/microsoft/RIoT/blob/master/Reference/RIoT/RIoTCrypt/include/x509bldr.h#L22),
   * Only the KeyCertSign bit is set.
   *)
  `op_ku_with` x509_KU_DIGITAL_SIGNATURE
  `op_ku_with` x509_KU_CRL_SIGN

// inline_for_extraction
// let alg_DeviceID = AlgID_Ed25519

// inline_for_extraction
// let alg_AliasKey = AlgID_Ed25519
