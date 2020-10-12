module ASN1.Low.Value.UTC_TIME

open ASN1.Low.Base

open ASN1.Base
open ASN1.Low.Tag
open ASN1.Low.Length
open ASN1.Low.Bytes32
open ASN1.Spec.Value.UTC_TIME

open FStar.Integers

module B32 = FStar.Bytes

val serialize32_asn1_utc_time_backwards
: serializer32_backwards (serialize_asn1_utc_time)

val serialize32_asn1_utc_time_TLV_backwards
: serializer32_backwards (serialize_asn1_utc_time_TLV)
