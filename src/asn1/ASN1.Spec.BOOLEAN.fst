module ASN1.Spec.BOOLEAN

include LowParse.Spec.Base
include LowParse.Spec.Combinators
include LowParse.Spec.Int
friend  LowParse.Spec.Int

include ASN1.Base

(* BOOLEAN primitive *)
let encode_asn1_boolean
  (b: bool)
: Tot byte
= match b with
  | true  -> 0xFFuy
  | false -> 0x00uy

let decode_asn1_boolean
  (bs: bytes{Seq.length bs == 1})
: Tot (option bool)
= match bs.[0] with
  | 0xFFuy -> Some true
  | 0x00uy -> Some false
  | _      -> None

let decode_asn1_boolean_injective ()
: Lemma (
  make_constant_size_parser_precond 1 bool decode_asn1_boolean
) = ()

let parse_asn1_boolean
: parser parse_asn1_boolean_kind bool
= decode_asn1_boolean_injective ();
  make_constant_size_parser 1 bool decode_asn1_boolean

let parse_asn1_boolean_unfold
  (input: bytes)
: Lemma (
  parse parse_asn1_boolean input ==
 (match parse parse_u8 input with
  | Some (0xFFuy, 1) -> Some (true,  1)
  | Some (0x00uy, 1) -> Some (false, 1)
  | _                -> None)
) = ()

let serialize_asn1_boolean
: serializer parse_asn1_boolean
= fun (b: bool) -> Seq.create 1 (encode_asn1_boolean b)
