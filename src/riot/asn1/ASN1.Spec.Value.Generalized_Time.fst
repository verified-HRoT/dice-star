module ASN1.Spec.Value.Generalized_Time

open ASN1.Spec.Base

open ASN1.Base
open ASN1.Spec.Tag
open ASN1.Spec.Length
open ASN1.Spec.Bytes32

open FStar.Integers

module B32 = FStar.Bytes

#set-options "--z3rlimit 32  --fuel 0 --ifuel 0"

let parse_asn1_generalized_time
: parser parse_asn1_generalized_time_kind (datatype_of_asn1_type Generalized_Time)
= parse_flbytes32 15ul
  `parse_filter`
  valid_generalized_time

let serialize_asn1_generalized_time
: serializer (parse_asn1_generalized_time)
= serialize_flbytes32 15ul
  `serialize_filter`
  valid_generalized_time

inline_for_extraction
let parser_tag_of_generalized_time
  (x: datatype_of_asn1_type Generalized_Time)
: Tot (the_asn1_tag Generalized_Time `tuple2` asn1_value_int32_of_type Generalized_Time)
= (Generalized_Time, 15ul)

#push-options "--ifuel 1"
let synth_asn1_oid_V
  (tag: the_asn1_tag Generalized_Time `tuple2` asn1_value_int32_of_type Generalized_Time)
  (x: datatype_of_asn1_type Generalized_Time)
: GTot (refine_with_tag parser_tag_of_generalized_time tag)
= x
#pop-options

inline_for_extraction
let synth_asn1_oid_V_inverse
  (tag: the_asn1_tag Generalized_Time `tuple2` asn1_value_int32_of_type Generalized_Time)
  (x': refine_with_tag parser_tag_of_generalized_time tag)
: Tot (x: datatype_of_asn1_type Generalized_Time
          { x' == synth_asn1_oid_V tag x })
= x'

let parse_asn1_generalized_time_TLV
= parse_tagged_union
  (* pt *) (parse_asn1_tag_of_type Generalized_Time
            `nondep_then`
            parse_asn1_length_of_type Generalized_Time)
  (* tg *) (parser_tag_of_generalized_time)
  (* pd *) (fun tag -> parse_asn1_generalized_time `parse_synth` synth_asn1_oid_V tag)

let serialize_asn1_generalized_time_TLV
= serialize_tagged_union
  (* st *) (serialize_asn1_tag_of_type Generalized_Time
            `serialize_nondep_then`
            serialize_asn1_length_of_type Generalized_Time)
  (* tg *) (parser_tag_of_generalized_time)
  (* sd *) (fun tag -> serialize_synth
                       (parse_asn1_generalized_time)
                       (synth_asn1_oid_V tag)
                       (serialize_asn1_generalized_time)
                       (synth_asn1_oid_V_inverse tag)
                       ())

let lemma_serialize_asn1_generalized_time_TLV_unfold
  (x: datatype_of_asn1_type Generalized_Time)
: Lemma (
  serialize_asn1_generalized_time_TLV `serialize` x ==
 (serialize_asn1_tag_of_type Generalized_Time `serialize` Generalized_Time)
  `Seq.append`
 (serialize_asn1_length_of_type Generalized_Time `serialize` 15ul)
  `Seq.append`
 (serialize_flbytes32 15ul `serialize` x)
)
= let tag = parser_tag_of_generalized_time x in
  serialize_nondep_then_eq
  (* s1 *) (serialize_asn1_tag_of_type Generalized_Time)
  (* s2 *) (serialize_asn1_length_of_type Generalized_Time)
  (* in *) (tag);
  serialize_synth_eq
    (parse_asn1_generalized_time)
    (synth_asn1_oid_V tag)
    (serialize_asn1_generalized_time)
    (synth_asn1_oid_V_inverse tag)
    ()
    (x);
  serialize_tagged_union_eq
  (* st *) (serialize_asn1_tag_of_type Generalized_Time
            `serialize_nondep_then`
            serialize_asn1_length_of_type Generalized_Time)
  (* tg *) (parser_tag_of_generalized_time)
  (* sd *) (fun tag -> serialize_synth
                       (parse_asn1_generalized_time)
                       (synth_asn1_oid_V tag)
                       (serialize_asn1_generalized_time)
                       (synth_asn1_oid_V_inverse tag)
                       ())
  (* in *) (x)

let lemma_serialize_asn1_generalized_time_TLV_size
  (x: datatype_of_asn1_type Generalized_Time)
: Lemma (
  length_of_opaque_serialization serialize_asn1_generalized_time_TLV x == 17
)
= lemma_serialize_asn1_generalized_time_TLV_unfold x

