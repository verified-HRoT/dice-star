module ASN1.Spec.Value.UTC_TIME

open ASN1.Spec.Base

open ASN1.Base
open ASN1.Spec.Tag
open ASN1.Spec.Length
open ASN1.Spec.Bytes32

open FStar.Integers

module B32 = FStar.Bytes

#set-options "--z3rlimit 32  --fuel 0 --ifuel 0"

let parse_asn1_utc_time
: parser parse_asn1_utc_time_kind (datatype_of_asn1_type UTC_TIME)
= parse_flbytes32 13ul
  `parse_filter`
  valid_utc_time

let serialize_asn1_utc_time
: serializer (parse_asn1_utc_time)
= serialize_flbytes32 13ul
  `serialize_filter`
  valid_utc_time

inline_for_extraction
let parser_tag_of_utc_time
  (x: datatype_of_asn1_type UTC_TIME)
: Tot (the_asn1_tag UTC_TIME `tuple2` asn1_value_int32_of_type UTC_TIME)
= (UTC_TIME, 13ul)

#push-options "--ifuel 1"
let synth_asn1_oid_V
  (tag: the_asn1_tag UTC_TIME `tuple2` asn1_value_int32_of_type UTC_TIME)
  (x: datatype_of_asn1_type UTC_TIME)
: GTot (refine_with_tag parser_tag_of_utc_time tag)
= x
#pop-options

inline_for_extraction
let synth_asn1_oid_V_inverse
  (tag: the_asn1_tag UTC_TIME `tuple2` asn1_value_int32_of_type UTC_TIME)
  (x': refine_with_tag parser_tag_of_utc_time tag)
: Tot (x: datatype_of_asn1_type UTC_TIME
          { x' == synth_asn1_oid_V tag x })
= x'

let parse_asn1_utc_time_TLV
= parse_tagged_union
  (* pt *) (parse_asn1_tag_of_type UTC_TIME
            `nondep_then`
            parse_asn1_length_of_type UTC_TIME)
  (* tg *) (parser_tag_of_utc_time)
  (* pd *) (fun tag -> parse_asn1_utc_time `parse_synth` synth_asn1_oid_V tag)

let serialize_asn1_utc_time_TLV
= serialize_tagged_union
  (* st *) (serialize_asn1_tag_of_type UTC_TIME
            `serialize_nondep_then`
            serialize_asn1_length_of_type UTC_TIME)
  (* tg *) (parser_tag_of_utc_time)
  (* sd *) (fun tag -> serialize_synth
                       (parse_asn1_utc_time)
                       (synth_asn1_oid_V tag)
                       (serialize_asn1_utc_time)
                       (synth_asn1_oid_V_inverse tag)
                       ())

let lemma_serialize_asn1_utc_time_TLV_unfold
  (x: datatype_of_asn1_type UTC_TIME)
: Lemma (
  serialize_asn1_utc_time_TLV `serialize` x ==
 (serialize_asn1_tag_of_type UTC_TIME `serialize` UTC_TIME)
  `Seq.append`
 (serialize_asn1_length_of_type UTC_TIME `serialize` 13ul)
  `Seq.append`
 (serialize_flbytes32 13ul `serialize` x)
)
= let tag = parser_tag_of_utc_time x in
  serialize_nondep_then_eq
  (* s1 *) (serialize_asn1_tag_of_type UTC_TIME)
  (* s2 *) (serialize_asn1_length_of_type UTC_TIME)
  (* in *) (tag);
  serialize_synth_eq
    (parse_asn1_utc_time)
    (synth_asn1_oid_V tag)
    (serialize_asn1_utc_time)
    (synth_asn1_oid_V_inverse tag)
    ()
    (x);
  serialize_tagged_union_eq
  (* st *) (serialize_asn1_tag_of_type UTC_TIME
            `serialize_nondep_then`
            serialize_asn1_length_of_type UTC_TIME)
  (* tg *) (parser_tag_of_utc_time)
  (* sd *) (fun tag -> serialize_synth
                       (parse_asn1_utc_time)
                       (synth_asn1_oid_V tag)
                       (serialize_asn1_utc_time)
                       (synth_asn1_oid_V_inverse tag)
                       ())
  (* in *) (x)

let lemma_serialize_asn1_utc_time_TLV_size
  (x: datatype_of_asn1_type UTC_TIME)
: Lemma (
  length_of_opaque_serialization serialize_asn1_utc_time_TLV x == 15
)
= lemma_serialize_asn1_utc_time_TLV_unfold x
