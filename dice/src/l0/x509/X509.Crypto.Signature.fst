module X509.Crypto.Signature

open ASN1.Spec
open ASN1.Low
open X509.Base
open FStar.Integers

#set-options "--fuel 0 --ifuel 0"

let parse_x509_signature
= parse_asn1_TLV_of_type BIT_STRING
  `parse_filter`
  filter_x509_signature

let serialize_x509_signature
= serialize_asn1_TLV_of_type BIT_STRING
  `serialize_filter`
  filter_x509_signature

let lemma_serialize_x509_signature_unfold x = ()

let lemma_serialize_x509_signature_size x
= lemma_serialize_x509_signature_unfold x;
  lemma_serialize_asn1_bit_string_TLV_size x

let serialize32_x509_signature_backwards
= serialize32_asn1_bit_string_TLV_backwards ()
  `serialize32_filter_backwards`
  filter_x509_signature
