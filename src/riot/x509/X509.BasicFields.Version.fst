module X509.BasicFields.Version

open LowParse.Low.Base

open ASN1.Spec
open ASN1.Low

open X509.Base

open FStar.Integers

#set-options "--z3rlimit 32 --fuel 0 --ifuel 0"

let filter_x509_version
  (x: datatype_of_asn1_type INTEGER)
: GTot bool
= 0l <= x && x <= 2l

let x509_version_payload_t: Type
= parse_filter_refine filter_x509_version

let parse_x509_version_payload
: parser _ x509_version_payload_t
= parse_asn1_TLV_of_type INTEGER
  `parse_filter`
  filter_x509_version

let serialize_x509_version_payload
: serializer parse_x509_version_payload
= serialize_asn1_TLV_of_type INTEGER
  `serialize_filter`
  filter_x509_version

let lemma_serialize_x509_version_payload_unfold
  (x: x509_version_payload_t)
= lemma_serialize_asn1_integer_TLV_unfold x

let lemma_serialize_x509_version_payload_size
  (x: x509_version_payload_t)
= lemma_serialize_asn1_integer_TLV_size x

let lemma_serialize_x509_version_payload_size_exact
  (x: x509_version_payload_t)
: Lemma (length_of_opaque_serialization serialize_x509_version_payload x == 3)
= lemma_serialize_asn1_integer_TLV_size x;
  assert (length_of_opaque_serialization serialize_x509_version_payload x == length_of_asn1_primitive_TLV #INTEGER x)

let serialize32_x509_version_payload_backwards
: serializer32_backwards serialize_x509_version_payload
= serialize32_asn1_TLV_backwards_of_type INTEGER
  `serialize32_filter_backwards`
  filter_x509_version

let length_of_x509_version_payload ()
: GTot (l: asn1_value_length_of_type SEQUENCE
           { forall (x: x509_version_payload_t). l == length_of_opaque_serialization serialize_x509_version_payload x })
= Classical.forall_intro lemma_serialize_x509_version_payload_size_exact;
  3

let len_of_x509_version_payload ()
: Tot (len: asn1_value_int32_of_type SEQUENCE
           { forall (x: x509_version_payload_t). v len == length_of_opaque_serialization serialize_x509_version_payload x })
= Classical.forall_intro lemma_serialize_x509_version_payload_size_exact;
  3ul


let x509_version_t: Type
= CUSTOM_TAG CONTEXT_SPECIFIC CONSTRUCTED 0uy
  `inbound_envelop_tag_with_value_of`
  serialize_x509_version_payload

noextract inline_for_extraction
let x509_version_1: x509_version_t = 0l

noextract inline_for_extraction
let x509_version_2: x509_version_t = 1l

noextract inline_for_extraction
let x509_version_3: x509_version_t = 2l

let parse_x509_version
: parser _ x509_version_t
= CUSTOM_TAG CONTEXT_SPECIFIC CONSTRUCTED 0uy
  `parse_asn1_envelop_tag_with_TLV`
  serialize_x509_version_payload

let serialize_x509_version
: serializer parse_x509_version
= CUSTOM_TAG CONTEXT_SPECIFIC CONSTRUCTED 0uy
  `serialize_asn1_envelop_tag_with_TLV`
  serialize_x509_version_payload

let lemma_serialize_x509_version_unfold
  (x: x509_version_t)
: Lemma (
  predicate_serialize_asn1_envelop_tag_with_TLV_unfold
    (CUSTOM_TAG CONTEXT_SPECIFIC CONSTRUCTED 0uy)
    (serialize_x509_version_payload)
    (x)
)
= lemma_serialize_asn1_envelop_tag_with_TLV_unfold
    (CUSTOM_TAG CONTEXT_SPECIFIC CONSTRUCTED 0uy)
    (serialize_x509_version_payload)
    (x)

let lemma_serialize_x509_version_size
  (x: x509_version_t)
: Lemma (
  predicate_serialize_asn1_envelop_tag_with_TLV_size
    (CUSTOM_TAG CONTEXT_SPECIFIC CONSTRUCTED 0uy)
    (serialize_x509_version_payload)
    (x)
)
= lemma_serialize_asn1_envelop_tag_with_TLV_size
    (CUSTOM_TAG CONTEXT_SPECIFIC CONSTRUCTED 0uy)
    (serialize_x509_version_payload)
    (x)

let lemma_serialize_x509_version_size_exact
  (x: x509_version_t)
: Lemma (
  length_of_opaque_serialization serialize_x509_version x ==
  5
)
= lemma_serialize_x509_version_size x;
  lemma_serialize_x509_version_payload_size_exact x

let length_of_x509_version ()
: GTot (l: asn1_value_length_of_type SEQUENCE
           { forall (x: x509_version_t).
               let _ = lemma_serialize_x509_version_size_exact x in
               l == length_of_opaque_serialization serialize_x509_version x })
= Classical.forall_intro lemma_serialize_x509_version_size_exact;
  5

let len_of_x509_version ()
: Tot (len: asn1_value_int32_of_type SEQUENCE
           { forall (x: x509_version_t).
               let _ = lemma_serialize_x509_version_size_exact x in
               v len == length_of_opaque_serialization serialize_x509_version x })
= Classical.forall_intro lemma_serialize_x509_version_size_exact;
  5ul

let serialize32_x509_version_backwards
: serializer32_backwards serialize_x509_version
= CUSTOM_TAG CONTEXT_SPECIFIC CONSTRUCTED 0uy
  `serialize32_asn1_envelop_tag_with_TLV_backwards`
  serialize32_x509_version_payload_backwards

let x509_get_version
  (x: x509_version_payload_t)
: Tot (x509_version_t)
= x
