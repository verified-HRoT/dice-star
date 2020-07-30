module ASN1.Low.Value.NULL

open ASN1.Base
open ASN1.Spec.Value.NULL
open ASN1.Low.Base

open FStar.Integers

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module MB = LowStar.Monotonic.Buffer
module B = LowStar.Buffer
module Cast = FStar.Int.Cast

(* NOTE: Read after `ASN1.Spec.Tag`, `ASN1.Spec.Length` *)

inline_for_extraction
let serialize32_asn1_ASN1_NULL_backwards ()
: Tot (serializer32_backwards serialize_asn1_ASN1_NULL)
= fun (_: datatype_of_asn1_type ASN1_NULL)
    (#rrel #rel: _)
    (b: B.mbuffer byte rrel rel)
    (pos: size_t)
-> 0ul

open ASN1.Spec.Tag
open ASN1.Spec.Length
open ASN1.Low.Tag
open ASN1.Low.Length

inline_for_extraction
let synth_asn1_ASN1_NULL_TLV_inverse_impl
  (x: datatype_of_asn1_type ASN1_NULL)
: Tot (a: ((the_asn1_tag ASN1_NULL & asn1_value_int32_of_type ASN1_NULL) & datatype_of_asn1_type ASN1_NULL){a == synth_asn1_ASN1_NULL_TLV_inverse x})
= ((ASN1_NULL, 0ul), x)

// inline_for_extraction
let serialize32_asn1_ASN1_NULL_TLV_backwards ()
: Tot (serializer32_backwards serialize_asn1_ASN1_NULL_TLV)
= serialize32_synth_backwards
   (* ls1*) (serialize32_asn1_tag_of_type_backwards ASN1_NULL
             `serialize32_nondep_then_backwards`
             serialize32_asn1_length_of_type_backwards ASN1_NULL
             `serialize32_nondep_then_backwards`
             serialize32_asn1_ASN1_NULL_backwards ())
   (* f2 *) (synth_asn1_ASN1_NULL_TLV)
   (* g1 *) (synth_asn1_ASN1_NULL_TLV_inverse)
   (* lg1*) (synth_asn1_ASN1_NULL_TLV_inverse_impl)
   (* Prf*) ()
