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
= fun (_: unit)
    (#rrel #rel: _)
    (b: B.mbuffer byte_t rrel rel)
    (pos: size_t)
-> 0ul
