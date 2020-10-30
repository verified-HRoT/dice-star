module L0.X509.Base
open ASN1.Spec
open L0.Base
open X509

module B32 = FStar.Bytes

#set-options "--__temp_no_proj L0.X509.Base"

noeq
type deviceIDCSR_ingredients_t = {
  deviceIDCSR_ku: key_usage_payload_t;
  deviceIDCSR_version: datatype_of_asn1_type INTEGER;
  deviceIDCSR_s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING;
  deviceIDCSR_s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING;
  deviceIDCSR_s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING
}

noeq
type aliasKeyCRT_ingredients_t = {
  aliasKeyCrt_version: x509_version_t;
  aliasKeyCrt_serialNumber: x509_serialNumber_t;
  aliasKeyCrt_i_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING;
  aliasKeyCrt_i_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING;
  aliasKeyCrt_i_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING;
  aliasKeyCrt_notBefore: datatype_of_asn1_type UTC_TIME;
  aliasKeyCrt_notAfter : datatype_of_asn1_type Generalized_Time;
  aliasKeyCrt_s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING;
  aliasKeyCrt_s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING;
  aliasKeyCrt_s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING;
  aliasKeyCrt_ku: key_usage_payload_t;
  aliasKeyCrt_l0_version: datatype_of_asn1_type INTEGER;
}

let aliasKeyCrt_key_usage: key_usage_payload_t
= normalize_term (x509_KU_KEY_CERT_SIGN
  (*
   * Adding more key usage bits for test only. According to the
   * [reference implementation](https://github.com/microsoft/L0/blob/master/Reference/L0/RIoTCrypt/include/x509bldr.h#L22),
   * Only the KeyCertSign bit is set.
   *)
  // `op_ku_with` x509_KU_DIGITAL_SIGNATURE
  // `op_ku_with` x509_KU_CRL_SIGN
  )

// let sha1_digest_to_octet_string_spec
//   (s: lbytes_pub 20)
// : GTot (x: datatype_of_asn1_type OCTET_STRING
//            { dfst x == 20ul /\
//              B32.reveal (dsnd x) == s })
// = assert_norm (Seq.length s < pow2 32);
//   let s32: B32.lbytes 20 = B32.hide s in
//   B32.reveal_hide s;
//   assert (B32.reveal s32 == s);
//   (|20ul, s32|)


// inline_for_extraction
// let alg_DeviceID = AlgID_Ed25519

// inline_for_extraction
// let alg_AliasKey = AlgID_Ed25519
