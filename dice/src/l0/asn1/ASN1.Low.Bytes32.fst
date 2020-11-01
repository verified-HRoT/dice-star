module ASN1.Low.Bytes32

open ASN1.Base
open ASN1.Spec.Bytes32
open ASN1.Low.Base
open LowParse.Low.Bytes
open FStar.Integers
module B32 = FStar.Bytes

let serialize32_flbytes32_backwards
  (len: asn1_int32)
: serializer32_backwards (serialize_flbytes32 len)
= fun (x: B32.lbytes32 len)
    #rrel #rel
    b pos
-> store_bytes x 0ul len b (pos - len);
   len
