module ASN1.Low.Value.Generalized_Time

open ASN1.Low.Base

open ASN1.Base
open ASN1.Low.Tag
open ASN1.Low.Length
open ASN1.Low.Bytes32
open ASN1.Spec.Value.Generalized_Time

open FStar.Integers

module B32 = FStar.Bytes

val serialize32_asn1_generalized_time_backwards
: serializer32_backwards (serialize_asn1_generalized_time)

val serialize32_asn1_generalized_time_TLV_backwards
: serializer32_backwards (serialize_asn1_generalized_time_TLV)
