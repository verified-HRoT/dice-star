module ASN1.Low.NULL

open ASN1.Base
open ASN1.Spec.NULL
open ASN1.Low.Base

open FStar.Integers

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module MB = LowStar.Monotonic.Buffer
module B = LowStar.Buffer
module Cast = FStar.Int.Cast

let serialize32_asn1_null_backwards ()
: Tot (serializer32_backwards serialize_asn1_null)
= fun (_: datatype_of_asn1_type NULL)
    (#rrel #rel: _)
    (b: B.mbuffer byte_t rrel rel)
    (pos: size_t)
-> 0ul

open ASN1.Spec.Tag
open ASN1.Spec.Length
open ASN1.Low.Tag
open ASN1.Low.Length

let synth_asn1_null_TLV_inverse_impl
  (x: datatype_of_asn1_type NULL)
: Tot (a: ((the_asn1_type NULL & asn1_int32_of_type NULL) & datatype_of_asn1_type NULL){a == synth_asn1_null_TLV_inverse x})
= ((NULL, 0ul), x)

let serialize32_asn1_null_TLV_backwards ()
: Tot (serializer32_backwards serialize_asn1_null_TLV)
= serialize32_synth_backwards
   (* ls1*) (serialize32_the_asn1_tag_backwards NULL
             `serialize32_nondep_then_backwards`
             serialize32_asn1_length_of_type_backwards NULL
             `serialize32_nondep_then_backwards`
             serialize32_asn1_null_backwards ())
   (* f2 *) (synth_asn1_null_TLV)
   (* g1 *) (synth_asn1_null_TLV_inverse)
   (* lg1*) (synth_asn1_null_TLV_inverse_impl)
   (* Prf*) ()
