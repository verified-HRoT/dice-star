module X509.BasicFields.Version

open LowParse.Low.Base

open ASN1.Spec
open ASN1.Low

open X509.Base

open FStar.Integers

#set-options "--z3rlimit 32 --fuel 0 --ifuel 0"

let parse_x509_version_payload
= parse_asn1_TLV_of_type INTEGER
  `parse_filter`
  filter_x509_version

let serialize_x509_version_payload
= serialize_asn1_TLV_of_type INTEGER
  `serialize_filter`
  filter_x509_version


let lemma_serialize_x509_version_payload_size_exact x
= lemma_serialize_asn1_integer_TLV_size x;
  assert (length_of_opaque_serialization serialize_x509_version_payload x == length_of_asn1_primitive_TLV #INTEGER x)

let serialize32_x509_version_payload_backwards
= serialize32_asn1_TLV_backwards_of_type INTEGER
  `serialize32_filter_backwards`
  filter_x509_version

noextract inline_for_extraction
let x509_version_1: x509_version_t = 0l

noextract inline_for_extraction
let x509_version_2: x509_version_t = 1l

noextract inline_for_extraction
let x509_version_3: x509_version_t = 2l

let lemma_serialize_x509_version_unfold x
= lemma_serialize_asn1_envelop_tag_with_TLV_unfold
    (CUSTOM_TAG CONTEXT_SPECIFIC CONSTRUCTED 0uy)
    (serialize_x509_version_payload)
    (x)

let lemma_serialize_x509_version_size x
= lemma_serialize_asn1_envelop_tag_with_TLV_size
    (CUSTOM_TAG CONTEXT_SPECIFIC CONSTRUCTED 0uy)
    (serialize_x509_version_payload)
    (x)

let lemma_serialize_x509_version_size_exact x
= lemma_serialize_x509_version_size x;
  lemma_serialize_x509_version_payload_size_exact x

let serialize32_x509_version_backwards
= CUSTOM_TAG CONTEXT_SPECIFIC CONSTRUCTED 0uy
  `serialize32_asn1_envelop_tag_with_TLV_backwards`
  serialize32_x509_version_payload_backwards
