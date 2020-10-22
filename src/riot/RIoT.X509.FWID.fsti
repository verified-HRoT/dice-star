module RIoT.X509.FWID

open LowParse.Low.Base
// open LowParse.Low.Combinators

open ASN1.Spec
open ASN1.Low

// open X509.Crypto
// open X509.BasicFields
// open X509.ExtFields

open FStar.Integers

#set-options "--z3rlimit 32 --fuel 0 --ifuel 0"

(* FWID
  ======
*)
type fwid_payload_t = {
  fwid_hashAlg: x:datatype_of_asn1_type OID {x == OID_DIGEST_SHA256}; (* OID *)
  fwid_value  : x:datatype_of_asn1_type OCTET_STRING {v (dfst x) == 32}
}

inline_for_extraction noextract
let parse_fwid_payload_kind
: parser_kind
= parse_filter_kind parse_asn1_oid_TLV_kind
  `and_then_kind`
  parse_filter_kind (parse_asn1_TLV_kind_of_type OCTET_STRING)

noextract
val parse_fwid_payload
: parser parse_fwid_payload_kind fwid_payload_t

noextract
val serialize_fwid_payload
: serializer parse_fwid_payload

val lemma_serialize_fwid_payload_unfold
  (x: fwid_payload_t)
: Lemma (
  serialize serialize_fwid_payload x ==
  serialize serialize_asn1_oid_TLV x.fwid_hashAlg
  `Seq.append`
  serialize serialize_asn1_octet_string_TLV x.fwid_value
)

val lemma_serialize_fwid_payload_size
  (x: fwid_payload_t)
: Lemma (
  Seq.length (serialize serialize_fwid_payload x) ==
  length_of_asn1_primitive_TLV x.fwid_hashAlg +
  length_of_asn1_primitive_TLV x.fwid_value /\
  Seq.length (serialize serialize_fwid_payload x) == 45
)

(* inbound sub type*)
let fwid_t
= inbound_sequence_value_of serialize_fwid_payload

(* TLV serializer *)
noextract
let parse_fwid
: parser (parse_asn1_envelop_tag_with_TLV_kind SEQUENCE) fwid_t
= fwid_t
  `coerce_parser`
  parse_asn1_sequence_TLV serialize_fwid_payload

noextract
let serialize_fwid
: serializer parse_fwid
= coerce_parser_serializer
  (* p *) (parse_fwid)
  (* s *) (serialize_asn1_sequence_TLV serialize_fwid_payload)
  (*prf*) ()

val lemma_serialize_fwid_unfold
  (x: fwid_t)
: Lemma ( predicate_serialize_asn1_sequence_TLV_unfold serialize_fwid_payload x )

val lemma_serialize_fwid_size
  (x: fwid_t)
: Lemma ( predicate_serialize_asn1_sequence_TLV_size serialize_fwid_payload x )

val lemma_serialize_fwid_size_exact
  (x: fwid_t)
: Lemma (
  length_of_opaque_serialization serialize_fwid x == 47
)

(* Low *)
noextract inline_for_extraction
val serialize32_fwid_payload_backwards
: serializer32_backwards serialize_fwid_payload

noextract inline_for_extraction
val serialize32_fwid_backwards
: serializer32_backwards serialize_fwid

module B32 = FStar.Bytes

(* helpers *)
let x509_get_fwid
  (fwid: B32.lbytes32 32ul)
: Tot (fwid_t)
=
  let fwid: fwid_payload_t = {
    fwid_hashAlg = OID_DIGEST_SHA256;
    fwid_value   = (|32ul, fwid|)
  } in
  (* Prf *) lemma_serialize_fwid_payload_size fwid;
  (* Prf *) (**) lemma_serialize_asn1_oid_TLV_size fwid.fwid_hashAlg;
  (* Prf *) (**) lemma_serialize_asn1_octet_string_TLV_size fwid.fwid_value;

(* return *) fwid
