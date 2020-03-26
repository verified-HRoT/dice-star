module ASN1.Spec.Tag

include LowParse.Spec.Base
include LowParse.Spec.Combinators
include LowParse.Spec.Int

include ASN1.Base

/// ASN.1 DER Tag Encoder
val asn1_tag_of_type: asn1_type -> Tot byte

val encode_asn1_tag: asn1_type -> Tot byte

/// Exposing ASN.1 DER Tag kind
let parse_asn1_tag_kind: parser_kind = constant_size_parser_kind 1


/// Generic ASN.1 DER Tag Decoder and Parser/Serializer
///
val decode_asn1_tag: s: bytes{Seq.length s == 1} -> Tot (option asn1_type)

val decode_asn1_tag_injective: unit -> Lemma (
  forall (s1: bytes {Seq.length s1 == 1})
    (s2: bytes {Seq.length s2 == 1}).
  {:pattern (decode_asn1_tag s1); (decode_asn1_tag s2)}
  let v1, v2 = decode_asn1_tag s1, decode_asn1_tag s2 in
  (Some? v1 \/ Some? v2) /\ v1 == v2
    ==> Seq.equal s1 s2)

val parse_asn1_tag: parser parse_asn1_tag_kind asn1_type

val parse_asn1_tag_unfold: input: bytes -> Lemma (
  parse parse_asn1_tag input ==
 (match parse parse_u8 input with
  | Some (x, 1) -> let d = decode_asn1_tag (Seq.create 1 x) in
                   if Some? d then Some (Some?.v d, 1) else None
  | _           -> None))

val serialize_asn1_tag: unit -> Tot (serializer parse_asn1_tag)


/// Specialized ASN.1 DER Tag Decoder and Parser/Serializer
///
val decode_the_asn1_tag: a: asn1_type -> b: bytes{Seq.length b == 1} -> Tot (option (the_asn1_type a))

val decode_the_asn1_tag_injective: a: asn1_type -> Lemma (
  forall (s1: bytes {Seq.length s1 == 1})
    (s2: bytes {Seq.length s2 == 1}).
  {:pattern (decode_the_asn1_tag a s1); (decode_the_asn1_tag a s2)}
  let v1, v2 = decode_the_asn1_tag a s1, decode_the_asn1_tag a s2 in
  (Some? v1 \/ Some? v2) /\ v1 == v2
    ==> Seq.equal s1 s2)

val parse_the_asn1_tag: a: asn1_type -> parser parse_asn1_tag_kind (the_asn1_type a)

val parse_the_asn1_tag_unfold: a: asn1_type -> input: bytes -> Lemma (
  parse (parse_the_asn1_tag a) input ==
 (match parse parse_u8 input with
  | Some (x, 1) -> if x = asn1_tag_of_type a then Some (a, 1) else None
  | _           -> None))

val serialize_the_asn1_tag: a: asn1_type -> Tot (serializer (parse_the_asn1_tag a))
