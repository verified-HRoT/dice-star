module ASN1.Low.Value.Generalized_Time

open ASN1.Low.Base

open ASN1.Base
open ASN1.Low.Tag
open ASN1.Low.Length
open ASN1.Low.Bytes32
open ASN1.Spec.Value.Generalized_Time

open FStar.Integers

module B32 = FStar.Bytes

#set-options "--fuel 0 --ifuel 2"

let serialize32_asn1_generalized_time_backwards
: serializer32_backwards (serialize_asn1_generalized_time)
= serialize32_flbytes32_backwards 15ul
  `serialize32_filter_backwards`
  valid_generalized_time

let serialize32_asn1_generalized_time_TLV_backwards
: serializer32_backwards (serialize_asn1_generalized_time_TLV)
= serialize32_synth_backwards
  (* s1 *) (serialize32_asn1_tag_of_type_backwards Generalized_Time
            `serialize32_nondep_then_backwards`
            serialize32_asn1_length_of_type_backwards Generalized_Time
            `serialize32_nondep_then_backwards`
            serialize32_asn1_generalized_time_backwards)
  (* f2 *) (synth_asn1_generalized_time_TLV)
  (* g1 *) (synth_asn1_generalized_time_TLV_inverse)
  (* g1'*) (synth_asn1_generalized_time_TLV_inverse)
  (* prf*) ()
