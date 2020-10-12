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
: serializer32_backwards (serialize_asn1_utc_time)
= serialize32_flbytes32_backwards 13ul
  `serialize32_filter_backwards`
  valid_utc_time

let serialize32_asn1_utc_time_TLV_backwards
: serializer32_backwards (serialize_asn1_utc_time_TLV)
= serialize32_synth_backwards
  (* s1 *) (serialize32_asn1_tag_of_type_backwards UTC_TIME
            `serialize32_nondep_then_backwards`
            serialize32_asn1_length_of_type_backwards UTC_TIME
            `serialize32_nondep_then_backwards`
            serialize32_asn1_utc_time_backwards)
  (* f2 *) (synth_asn1_utc_time_TLV)
  (* g1 *) (synth_asn1_utc_time_TLV_inverse)
  (* g1'*) (synth_asn1_utc_time_TLV_inverse)
  (* prf*) ()
