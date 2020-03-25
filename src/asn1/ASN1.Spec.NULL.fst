module ASN1.Spec.NULL

include LowParse.Spec.Base
include LowParse.Spec.Combinators

let parse_asn1_null
: parser parse_ret_kind unit
= parse_ret
  (* v *) ()

let serialize_asn1_null
: serializer parse_asn1_null
= serialize_ret
  (* v *) ()
  (*prf*) (fun n -> ())
