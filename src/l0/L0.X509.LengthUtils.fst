module L0.X509.LengthUtils

open ASN1.Spec
open X509
open FStar.Integers

#set-options "--z3rlimit 64 --fuel 0 --ifuel 0 --using_facts_from '* -FStar.Tactics -FStar.Reflection'"

// let lemma_length_of_aliasKeyTBS_issuer_payload
//   (s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING)
//   (s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
//   (s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING)
//   : Lemma
//       ((v (len_of_RDN_x520_attribute s_common) +
//         v (len_of_RDN_x520_attribute s_org) +
//         v (len_of_RDN_x520_attribute s_country)) <= asn1_value_length_max_of_type SEQUENCE)
//   = ()

let lemma_length_of_l0_extension (version:datatype_of_asn1_type INTEGER)
  : Lemma (length_of_TLV SEQUENCE (length_of_asn1_primitive_TLV version + 109) <=
           asn1_value_length_max_of_type SEQUENCE)
  = ()

let lemma_length_of_l0_extension_riot_version (x:datatype_of_asn1_type INTEGER)
  : Lemma (length_of_TLV SEQUENCE (length_of_asn1_primitive_TLV x + 110) <= 118)
  = ()

unfold noextract
let coerce_x509_rdn_attribute_t_string_to_asn1_string_cn
  (x:x509_RDN_x520_attribute_string_t COMMON_NAME IA5_STRING)
  : y:datatype_of_asn1_type IA5_STRING{
      x520_attribute_lb COMMON_NAME <= dfst y /\
      dfst y <= x520_attribute_ub COMMON_NAME
    }
  = x

unfold noextract
let coerce_x509_rdn_attribute_t_string_to_asn1_string_org
  (x:x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING)
  : y:datatype_of_asn1_type IA5_STRING{
      x520_attribute_lb ORGANIZATION <= dfst y /\
      dfst y <= x520_attribute_ub ORGANIZATION
    }
  = x

unfold noextract
let coerce_x509_rdn_attribute_t_string_to_asn1_string_country
  (x:x509_RDN_x520_attribute_string_t COUNTRY PRINTABLE_STRING)
  : y:datatype_of_asn1_type PRINTABLE_STRING{
      x520_attribute_lb COUNTRY <= dfst y /\
      dfst y <= x520_attribute_ub COUNTRY
    }
  = x
