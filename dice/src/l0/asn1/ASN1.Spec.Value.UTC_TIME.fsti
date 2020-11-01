module ASN1.Spec.Value.UTC_TIME

open ASN1.Spec.Base

open ASN1.Base
open ASN1.Spec.Tag
open ASN1.Spec.Length
open ASN1.Spec.Bytes32

open FStar.Integers

module B32 = FStar.Bytes

#set-options "--z3rlimit 32  --fuel 0 --ifuel 0"

inline_for_extraction noextract
let parse_asn1_utc_time_kind: parser_kind
= parse_filter_kind (total_constant_size_parser_kind 13)

val parse_asn1_utc_time
: parser parse_asn1_utc_time_kind (datatype_of_asn1_type UTC_TIME)

val serialize_asn1_utc_time
: serializer (parse_asn1_utc_time)


inline_for_extraction noextract
let parse_asn1_utc_time_TLV_kind
: parser_kind
= parse_asn1_tag_kind
  `and_then_kind`
  parse_asn1_length_kind_of_type UTC_TIME
  `and_then_kind`
  parse_asn1_utc_time_kind

val parse_asn1_utc_time_TLV
: parser parse_asn1_utc_time_TLV_kind (datatype_of_asn1_type UTC_TIME)

val serialize_asn1_utc_time_TLV
: serializer (parse_asn1_utc_time_TLV)

val lemma_serialize_asn1_utc_time_TLV_unfold
  (x: datatype_of_asn1_type UTC_TIME)
: Lemma (
  serialize_asn1_utc_time_TLV `serialize` x ==
 (serialize_asn1_tag_of_type UTC_TIME `serialize` UTC_TIME)
  `Seq.append`
 (serialize_asn1_length_of_type UTC_TIME `serialize` 13ul)
  `Seq.append`
 (serialize_flbytes32 13ul `serialize` x)
)

val lemma_serialize_asn1_utc_time_TLV_size
  (x: datatype_of_asn1_type UTC_TIME)
: Lemma (
  length_of_opaque_serialization serialize_asn1_utc_time_TLV x == 15
)
