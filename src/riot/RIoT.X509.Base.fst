module RIoT.X509.Base
open ASN1.Spec
open RIoT.Base
open X509.Base
open X509.ExtFields.KeyUsage

module B32 = FStar.Bytes

let aliasKeyCrt_key_usage: key_usage_payload_t
= normalize_term (x509_KU_KEY_CERT_SIGN
  (*
   * Adding more key usage bits for test only. According to the
   * [reference implementation](https://github.com/microsoft/RIoT/blob/master/Reference/RIoT/RIoTCrypt/include/x509bldr.h#L22),
   * Only the KeyCertSign bit is set.
   *)
  `op_ku_with` x509_KU_DIGITAL_SIGNATURE
  `op_ku_with` x509_KU_CRL_SIGN)

let sha1_digest_to_octet_string_spec
  (s: lbytes_pub 20)
: GTot (x: datatype_of_asn1_type OCTET_STRING
           { dfst x == 20ul /\
             B32.reveal (dsnd x) == s })
= assert_norm (Seq.length s < pow2 32);
  let s32: B32.lbytes 20 = B32.hide s in
  B32.reveal_hide s;
  assert (B32.reveal s32 == s);
  (|20ul, s32|)


// inline_for_extraction
// let alg_DeviceID = AlgID_Ed25519

// inline_for_extraction
// let alg_AliasKey = AlgID_Ed25519
