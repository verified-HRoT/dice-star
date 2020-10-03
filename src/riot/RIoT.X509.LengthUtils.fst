module RIoT.X509.LengthUtils

open ASN1.Spec
open X509
open FStar.Integers

#set-options "--z3rlimit 64 --fuel 0 --ifuel 0 --using_facts_from '* -FStar.Tactics -FStar.Reflection'"

let lemma_length_of_aliasKeyTBS_issuer_payload
  (s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
  (s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  (s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
  : Lemma
      ((length_of_RDN_x520_attribute s_common +
        length_of_RDN_x520_attribute s_org +
        length_of_RDN_x520_attribute s_country) <= asn1_value_length_max_of_type SEQUENCE)
  = ()

unfold noextract
let coerce_seq_to_x509_outermost_tag (x:asn1_TLV_length_of_type SEQUENCE)
  : (asn1_TLV_length_of_type x509_extensions_outmost_explicit_tag)
  = x

let lemma_length_of_riot_extension (version:datatype_of_asn1_type INTEGER)
  : Lemma (length_of_TLV SEQUENCE (length_of_asn1_primitive_TLV version + 109) <=
           asn1_value_length_max_of_type SEQUENCE)
  = ()

let lemma_length_of_riot_extension_riot_version (x:datatype_of_asn1_type INTEGER)
  : Lemma (length_of_TLV SEQUENCE (length_of_asn1_primitive_TLV x + 109) <= 117)
  = ()
