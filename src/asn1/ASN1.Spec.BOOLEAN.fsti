module ASN1.Spec.BOOLEAN

include LowParse.Spec.Base
include LowParse.Spec.Combinators
include LowParse.Spec.Int

include ASN1.Base

(* BOOLEAN primitive *)
val encode_asn1_boolean
  (b: bool)
: Tot byte

val decode_asn1_boolean
  (bs: bytes{Seq.length bs == 1})
: Tot (option bool)

val decode_asn1_boolean_injective: unit -> Lemma (
  make_constant_size_parser_precond 1 bool decode_asn1_boolean
)

(* NOTE: Expose kinds *)
let parse_asn1_boolean_kind: parser_kind = constant_size_parser_kind 1
val parse_asn1_boolean
: parser parse_asn1_boolean_kind bool

val parse_asn1_boolean_unfold
  (input: bytes)
: Lemma (
  parse parse_asn1_boolean input ==
 (match parse parse_u8 input with
  | Some (0xFFuy, 1) -> Some (true,  1)
  | Some (0x00uy, 1) -> Some (false, 1)
  | _                -> None)
)

val serialize_asn1_boolean
: serializer parse_asn1_boolean

// val synth_asn1_boolean_value: b: bool -> value: asn1_value{BOOLEAN_VALUE? value /\ BOOLEAN_VALUE}
