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

let synth_asn1_generalized_time_TLV
  (a: (the_asn1_tag Generalized_Time `tuple2`
       asn1_value_int32_of_type Generalized_Time) `tuple2`
       datatype_of_asn1_type Generalized_Time)
: GTot (datatype_of_asn1_type Generalized_Time)
= snd a

let synth_asn1_generalized_time_TLV_inverse
  (x: datatype_of_asn1_type Generalized_Time)
: Tot (a: ((the_asn1_tag Generalized_Time `tuple2`
             asn1_value_int32_of_type Generalized_Time) `tuple2`
             datatype_of_asn1_type Generalized_Time)
           { x == synth_asn1_generalized_time_TLV a })
= ((Generalized_Time, 15ul), x)

#push-options "--ifuel 2"
let parse_asn1_generalized_time_TLV
: parser parse_asn1_generalized_time_TLV_kind (datatype_of_asn1_type Generalized_Time)
= parse_asn1_tag_of_type Generalized_Time
  `nondep_then`
  parse_asn1_length_of_type Generalized_Time
  `nondep_then`
  parse_asn1_generalized_time
  `parse_synth`
  synth_asn1_generalized_time_TLV

let serialize_asn1_generalized_time_TLV
: serializer (parse_asn1_generalized_time_TLV)
= serialize_synth
  (* p1 *) (parse_asn1_tag_of_type Generalized_Time
            `nondep_then`
            parse_asn1_length_of_type Generalized_Time
            `nondep_then`
            parse_asn1_generalized_time)
  (* f2 *) (synth_asn1_generalized_time_TLV)
  (* s1 *) (serialize_asn1_tag_of_type Generalized_Time
            `serialize_nondep_then`
            serialize_asn1_length_of_type Generalized_Time
            `serialize_nondep_then`
            serialize_asn1_generalized_time)
  (* g1 *) (synth_asn1_generalized_time_TLV_inverse)
  (* prf*) ()

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
= serialize_nondep_then_eq
  (* s1 *) (serialize_asn1_tag_of_type Generalized_Time)
  (* s2 *) (serialize_asn1_length_of_type Generalized_Time)
  (* in *) (fst (synth_asn1_generalized_time_TLV_inverse x));
  serialize_nondep_then_eq
  (* s1 *) (serialize_asn1_tag_of_type Generalized_Time
            `serialize_nondep_then`
            serialize_asn1_length_of_type Generalized_Time)
  (* s2 *) (serialize_asn1_generalized_time)
  (* in *) (synth_asn1_generalized_time_TLV_inverse x);
  serialize_synth_eq
  (* p1 *) (parse_asn1_tag_of_type Generalized_Time
            `nondep_then`
            parse_asn1_length_of_type Generalized_Time
            `nondep_then`
            parse_asn1_generalized_time)
  (* f2 *) (synth_asn1_generalized_time_TLV)
  (* s1 *) (serialize_asn1_tag_of_type Generalized_Time
            `serialize_nondep_then`
            serialize_asn1_length_of_type Generalized_Time
            `serialize_nondep_then`
            serialize_asn1_generalized_time)
  (* g1 *) (synth_asn1_generalized_time_TLV_inverse)
  (* prf*) ()
  (* in *) (x)

let lemma_serialize_asn1_generalized_time_TLV_size
  (x: datatype_of_asn1_type Generalized_Time)
: Lemma (
  length_of_opaque_serialization serialize_asn1_generalized_time_TLV x == 17
)
= lemma_serialize_asn1_generalized_time_TLV_unfold x
#pop-options
