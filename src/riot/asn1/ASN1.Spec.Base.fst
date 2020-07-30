module ASN1.Spec.Base

include LowParse.Spec.Base
include LowParse.Spec.Combinators

unfold
let coerce_parser_serializer
  (#t2: Type0)
  (#k: parser_kind)
  (#t1: Type0)
  (#p1: parser k t1)
  (p2: parser k t2)
  (s: serializer p1)
  (u: unit { t2 == t1 /\ p2 == coerce_parser t2 p1} )
: Tot (serializer (p2))
= s

unfold
let length_of_opaque_serialization
  (#t: Type0)
  (#k: parser_kind)
  (#p: parser k t)
  (s: serializer p)
  (x: t)
= Seq.length (s `serialize` x)
