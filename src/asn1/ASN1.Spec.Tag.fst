module ASN1.Spec.Tag

include LowParse.Spec.Base
include LowParse.Spec.Combinators
include LowParse.Spec.Int
friend  LowParse.Spec.Int

include ASN1.Base

(* Tag parser primitive *)

/// ASN.1 DER Tag Encoder
let asn1_tag_of_type
  (a: asn1_type)
: Tot byte
= match a with
  | BOOLEAN      -> 0x01uy
  // | INTEGER      -> 0x02uy
  // | BIT_STRING   -> 0x03uy
  | OCTET_STRING -> 0x04uy
  // | NULL         -> 0x05uy
  // | OID          -> 0x06uy
  // | SEQUENCE     -> 0x30uy

let encode_asn1_tag
= fun (a: asn1_type) -> Seq.create 1 (asn1_tag_of_type a)

/// Generic ASN.1 DER Tag Parser
///

let decode_asn1_tag
  (b: bytes {Seq.length b == 1})
: Tot (option (asn1_type))
= match b.[0] with
  | 0x01uy -> Some BOOLEAN
  // | 0x02uy -> Some INTEGER
  // | 0x03uy -> Some BIT_STRING
  | 0x04uy -> Some OCTET_STRING
  // | 0x05uy -> Some NULL
  // | 0x06uy -> Some OID
  // | 0x30uy -> Some SEQUENCE
  | _      -> None

let decode_asn1_tag_injective ()
: Lemma (
  forall (s1: bytes {Seq.length s1 == 1})
    (s2: bytes {Seq.length s2 == 1}).
  {:pattern (decode_asn1_tag s1); (decode_asn1_tag s2)}
  let v1, v2 = decode_asn1_tag s1, decode_asn1_tag s2 in
  (Some? v1 \/ Some? v2) /\ v1 == v2
  ==> Seq.equal s1 s2)
= ()

let parse_asn1_tag
: parser parse_asn1_tag_kind asn1_type
= decode_asn1_tag_injective ();
  make_constant_size_parser 1 asn1_type (decode_asn1_tag)

let parse_asn1_tag_unfold
  (input: bytes)
: Lemma (
  parse parse_asn1_tag input ==
 (match parse parse_u8 input with
  | Some (x, 1) -> let d = decode_asn1_tag (Seq.create 1 x) in
                   if Some? d then Some (Some?.v d, 1) else None
  | _           -> None))
= match parse parse_u8 input with
  | Some (x, 1) -> ()
  | _           -> ()

let serialize_asn1_tag ()
: Tot (serializer parse_asn1_tag)
= encode_asn1_tag

/// Specialized ASN.1 DER Tag Parser
///

/// Specialized decoder
let decode_the_asn1_tag
  (a: asn1_type)
  (b: bytes {Seq.length b == 1})
: Tot (option (the_asn1_type a))
= match a, b.[0] with
  | BOOLEAN      , 0x01uy -> Some BOOLEAN
  // | INTEGER      , 0x02uy -> Some INTEGER
  // | BIT_STRING   , 0x03uy -> Some BIT_STRING
  | OCTET_STRING , 0x04uy -> Some OCTET_STRING
  // | NULL         , 0x05uy -> Some NULL
  // | OID          , 0x06uy -> Some OID
  // | SEQUENCE     , 0x30uy -> Some SEQUENCE
  | _                     -> None

/// Decoder is injective
let decode_the_asn1_tag_injective
  (a: asn1_type)
: Lemma (
  forall (s1: bytes {Seq.length s1 == 1})
    (s2: bytes {Seq.length s2 == 1}).
  {:pattern (decode_the_asn1_tag a s1); (decode_the_asn1_tag a s2)}
  let v1, v2 = decode_the_asn1_tag a s1, decode_the_asn1_tag a s2 in
  (Some? v1 \/ Some? v2) /\ v1 == v2
  ==> Seq.equal s1 s2)
= ()

/// Specialized parser
let parse_the_asn1_tag
  (a:asn1_type)
: parser parse_asn1_tag_kind (the_asn1_type a)
= decode_the_asn1_tag_injective a;
  make_constant_size_parser 1 (the_asn1_type a) (decode_the_asn1_tag a)

let parse_the_asn1_tag_unfold
  (a: asn1_type)
  (input: bytes)
: Lemma (
  parse (parse_the_asn1_tag a) input ==
 (match parse parse_u8 input with
  | Some (x, 1) -> if x = asn1_tag_of_type a then Some (a, 1) else None
  | _           -> None))
= match parse parse_u8 input with
  | Some (x, 1) -> ()
  | _           -> ()

/// Specialized serializer
let serialize_the_asn1_tag
  (a: asn1_type)
: Tot (serializer (parse_the_asn1_tag a))
= fun (a': the_asn1_type a) -> encode_asn1_tag a'
