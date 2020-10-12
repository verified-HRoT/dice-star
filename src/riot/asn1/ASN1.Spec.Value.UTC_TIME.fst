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

let synth_asn1_utc_time_TLV
  (a: (the_asn1_tag UTC_TIME `tuple2`
       asn1_value_int32_of_type UTC_TIME) `tuple2`
       datatype_of_asn1_type UTC_TIME)
: GTot (datatype_of_asn1_type UTC_TIME)
= snd a

let synth_asn1_utc_time_TLV_inverse
  (x: datatype_of_asn1_type UTC_TIME)
: Tot (a: ((the_asn1_tag UTC_TIME `tuple2`
             asn1_value_int32_of_type UTC_TIME) `tuple2`
             datatype_of_asn1_type UTC_TIME)
           { x == synth_asn1_utc_time_TLV a })
= ((UTC_TIME, 13ul), x)

#push-options "--ifuel 2"
let parse_asn1_utc_time_TLV
: parser parse_asn1_utc_time_TLV_kind (datatype_of_asn1_type UTC_TIME)
= parse_asn1_tag_of_type UTC_TIME
  `nondep_then`
  parse_asn1_length_of_type UTC_TIME
  `nondep_then`
  parse_asn1_utc_time
  `parse_synth`
  synth_asn1_utc_time_TLV

let serialize_asn1_utc_time_TLV
: serializer (parse_asn1_utc_time_TLV)
= serialize_synth
  (* p1 *) (parse_asn1_tag_of_type UTC_TIME
            `nondep_then`
            parse_asn1_length_of_type UTC_TIME
            `nondep_then`
            parse_asn1_utc_time)
  (* f2 *) (synth_asn1_utc_time_TLV)
  (* s1 *) (serialize_asn1_tag_of_type UTC_TIME
            `serialize_nondep_then`
            serialize_asn1_length_of_type UTC_TIME
            `serialize_nondep_then`
            serialize_asn1_utc_time)
  (* g1 *) (synth_asn1_utc_time_TLV_inverse)
  (* prf*) ()

let lemma_serialize_asn1_utc_time_TLV_unfold x
= serialize_nondep_then_eq
  (* s1 *) (serialize_asn1_tag_of_type UTC_TIME)
  (* s2 *) (serialize_asn1_length_of_type UTC_TIME)
  (* in *) (fst (synth_asn1_utc_time_TLV_inverse x));
  serialize_nondep_then_eq
  (* s1 *) (serialize_asn1_tag_of_type UTC_TIME
            `serialize_nondep_then`
            serialize_asn1_length_of_type UTC_TIME)
  (* s2 *) (serialize_asn1_utc_time)
  (* in *) (synth_asn1_utc_time_TLV_inverse x);
  serialize_synth_eq
  (* p1 *) (parse_asn1_tag_of_type UTC_TIME
            `nondep_then`
            parse_asn1_length_of_type UTC_TIME
            `nondep_then`
            parse_asn1_utc_time)
  (* f2 *) (synth_asn1_utc_time_TLV)
  (* s1 *) (serialize_asn1_tag_of_type UTC_TIME
            `serialize_nondep_then`
            serialize_asn1_length_of_type UTC_TIME
            `serialize_nondep_then`
            serialize_asn1_utc_time)
  (* g1 *) (synth_asn1_utc_time_TLV_inverse)
  (* prf*) ()
  (* in *) (x)

let lemma_serialize_asn1_utc_time_TLV_size x
= lemma_serialize_asn1_utc_time_TLV_unfold x
#pop-options