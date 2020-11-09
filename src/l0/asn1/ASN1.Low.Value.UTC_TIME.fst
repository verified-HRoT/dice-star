module ASN1.Low.Value.UTC_TIME

open ASN1.Low.Base

open ASN1.Base
open ASN1.Low.Tag
open ASN1.Low.Length
open ASN1.Low.Bytes32
open ASN1.Spec.Value.UTC_TIME

open FStar.Integers

module B32 = FStar.Bytes

friend ASN1.Spec.Value.UTC_TIME

#set-options "--fuel 0 --ifuel 2"

let serialize32_asn1_utc_time_backwards
= serialize32_flbytes32_backwards 13ul
  `serialize32_filter_backwards`
  valid_utc_time

let serialize32_asn1_utc_time_TLV_backwards
= serialize32_tagged_union_backwards
  (* st32 *) (serialize32_asn1_tag_of_type_backwards UTC_TIME
              `serialize32_nondep_then_backwards`
              serialize32_asn1_length_of_type_backwards UTC_TIME)
  (* tg32 *) (parser_tag_of_utc_time)
  (* sd32 *) (fun tag -> serialize32_synth_backwards
                         (serialize32_asn1_utc_time_backwards)
                         (synth_asn1_oid_V tag)
                         (synth_asn1_oid_V_inverse tag)
                         (synth_asn1_oid_V_inverse tag)
                         ())
