module ASN1.Spec.Value.Generalized_Time

open ASN1.Spec.Base

open ASN1.Base
open ASN1.Spec.Tag
open ASN1.Spec.Length
open ASN1.Spec.Bytes32

open FStar.Integers

module B32 = FStar.Bytes

#set-options "--z3rlimit 32  --fuel 0 --ifuel 0"

inline_for_extraction noextract
let parse_asn1_generalized_time_kind: parser_kind
= parse_filter_kind (total_constant_size_parser_kind 15)

val parse_asn1_generalized_time
: parser parse_asn1_generalized_time_kind (datatype_of_asn1_type Generalized_Time)

val serialize_asn1_generalized_time
: serializer (parse_asn1_generalized_time)


inline_for_extraction noextract
let parse_asn1_generalized_time_TLV_kind
: parser_kind
= strong_parser_kind 17 17 None

val parse_asn1_generalized_time_TLV
: parser parse_asn1_generalized_time_TLV_kind (datatype_of_asn1_type Generalized_Time)

val serialize_asn1_generalized_time_TLV
: serializer (parse_asn1_generalized_time_TLV)

val lemma_serialize_asn1_generalized_time_TLV_unfold
  (x: datatype_of_asn1_type Generalized_Time)
: Lemma (
  serialize_asn1_generalized_time_TLV `serialize` x ==
 (serialize_asn1_tag_of_type Generalized_Time `serialize` Generalized_Time)
  `Seq.append`
 (serialize_asn1_length_of_type Generalized_Time `serialize` 15ul)
  `Seq.append`
 (serialize_flbytes32 15ul `serialize` x)
)

val lemma_serialize_asn1_generalized_time_TLV_size
  (x: datatype_of_asn1_type Generalized_Time)
: Lemma (
  length_of_opaque_serialization serialize_asn1_generalized_time_TLV x == 17
)
