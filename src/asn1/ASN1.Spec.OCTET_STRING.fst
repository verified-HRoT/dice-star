module ASN1.Spec.OCTET_STRING

open LowParse.Spec.Base
open LowParse.Spec.Combinators
open LowParse.Spec.SeqBytes.Base

open ASN1.Base

let parse_asn1_octet_string = parse_seq_flbytes

let serialize_asn1_octet_string = serialize_seq_flbytes
