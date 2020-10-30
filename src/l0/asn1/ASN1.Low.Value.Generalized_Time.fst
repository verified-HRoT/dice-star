module ASN1.Low.Value.Generalized_Time

open ASN1.Low.Base

open ASN1.Base
open ASN1.Low.Tag
open ASN1.Low.Length
open ASN1.Low.Bytes32
open ASN1.Spec.Value.Generalized_Time

open FStar.Integers

module B32 = FStar.Bytes

friend ASN1.Spec.Value.Generalized_Time

#set-options "--fuel 0 --ifuel 2"

let serialize32_asn1_generalized_time_backwards
= serialize32_flbytes32_backwards 15ul
  `serialize32_filter_backwards`
  valid_generalized_time

let serialize32_asn1_generalized_time_TLV_backwards
= serialize32_tagged_union_backwards
  (* st32 *) (serialize32_asn1_tag_of_type_backwards Generalized_Time
              `serialize32_nondep_then_backwards`
              serialize32_asn1_length_of_type_backwards Generalized_Time)
  (* tg32 *) (parser_tag_of_generalized_time)
  (* sd32 *) (fun tag -> serialize32_synth_backwards
                         (serialize32_asn1_generalized_time_backwards)
                         (synth_asn1_oid_V tag)
                         (synth_asn1_oid_V_inverse tag)
                         (synth_asn1_oid_V_inverse tag)
                         ())
