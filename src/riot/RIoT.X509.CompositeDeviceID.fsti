module RIoT.X509.CompositeDeviceID

open LowParse.Low.Base
open LowParse.Low.Combinators

open ASN1.Spec
open ASN1.Low

open X509.Base
open X509.BasicFields.SubjectPublicKeyInfo
open X509.Crypto
open RIoT.X509.Base
open RIoT.X509.FWID

#set-options "--z3rlimit 32 --fuel 0 --ifuel 0"

(* CompositeDeviceID *)
type compositeDeviceID_payload_t
= { riot_version : datatype_of_asn1_type INTEGER;
    riot_deviceID: subjectPublicKeyInfo_t;
    riot_fwid    : fwid_t }

noextract
let parse_compositeDeviceID_payload_kind
: parser_kind
= parse_asn1_TLV_kind_of_type INTEGER
  `and_then_kind`
  parse_asn1_envelop_tag_with_TLV_kind SEQUENCE
  `and_then_kind`
  parse_asn1_envelop_tag_with_TLV_kind SEQUENCE

noextract
val parse_compositeDeviceID_payload
: parser parse_compositeDeviceID_payload_kind (compositeDeviceID_payload_t)

noextract
val serialize_compositeDeviceID_payload
: serializer (parse_compositeDeviceID_payload)

val lemma_serialize_compositeDeviceID_payload_unfold
  (x: compositeDeviceID_payload_t)
: Lemma (
  serialize (serialize_compositeDeviceID_payload) x ==
  serialize (serialize_asn1_TLV_of_type INTEGER) x.riot_version
  `Seq.append`
  serialize (serialize_subjectPublicKeyInfo) x.riot_deviceID
  `Seq.append`
  serialize serialize_fwid x.riot_fwid
)

val lemma_serialize_compositeDeviceID_payload_size
  (x: compositeDeviceID_payload_t)
: Lemma (
  length_of_opaque_serialization (serialize_compositeDeviceID_payload) x ==
  length_of_asn1_primitive_TLV x.riot_version +
  length_of_opaque_serialization (serialize_subjectPublicKeyInfo) x.riot_deviceID +
  length_of_opaque_serialization serialize_fwid x.riot_fwid /\
  length_of_opaque_serialization serialize_compositeDeviceID_payload x ==
  length_of_asn1_primitive_TLV x.riot_version + 91 /\
  length_of_opaque_serialization serialize_compositeDeviceID_payload x <= 97
)

(* inbound sub type*)
let compositeDeviceID_t
= inbound_sequence_value_of (serialize_compositeDeviceID_payload)


(* TLV serializer *)
noextract
let parse_compositeDeviceID
: parser (parse_asn1_envelop_tag_with_TLV_kind SEQUENCE) (compositeDeviceID_t)
= compositeDeviceID_t
  `coerce_parser`
  parse_asn1_sequence_TLV (serialize_compositeDeviceID_payload)

noextract
let serialize_compositeDeviceID
: serializer (parse_compositeDeviceID)
= coerce_parser_serializer
  (* t *) (parse_compositeDeviceID)
  (* s *) (serialize_asn1_sequence_TLV (serialize_compositeDeviceID_payload))
  (*prf*) ()

(* manually unfolding `lemma_serialize_asn1_sequence_TLV_size` to avoid stuck here.  *)
val lemma_serialize_compositeDeviceID_unfold
  (x: compositeDeviceID_t)
: Lemma ( predicate_serialize_asn1_sequence_TLV_unfold serialize_compositeDeviceID_payload x )

val lemma_serialize_compositeDeviceID_size
  (x: compositeDeviceID_t)
: Lemma ( predicate_serialize_asn1_sequence_TLV_size serialize_compositeDeviceID_payload x )

open FStar.Integers
val lemma_serialize_compositeDeviceID_size_exact
  (x: compositeDeviceID_t)
: Lemma (
  length_of_opaque_serialization serialize_compositeDeviceID x ==
  length_of_asn1_primitive_TLV x.riot_version + 93 /\
  length_of_opaque_serialization serialize_compositeDeviceID_payload x <= 99
)

val serialize32_compositeDeviceID_payload_backwards
: serializer32_backwards (serialize_compositeDeviceID_payload)

val serialize32_compositeDeviceID_backwards
: serializer32_backwards (serialize_compositeDeviceID)

(* helpers *)
module B32 = FStar.Bytes

let x509_get_compositeDeviceID
  (version: datatype_of_asn1_type INTEGER)
  (deviceKeyPub: B32.lbytes32 32ul)
  (fwid: B32.lbytes32 32ul)
: Tot (compositeDeviceID_t)
= let deviceIDPublicKeyInfo: subjectPublicKeyInfo_t = x509_get_subjectPublicKeyInfo deviceKeyPub in
  (* Prf *) lemma_serialize_subjectPublicKeyInfo_size_exact deviceIDPublicKeyInfo;

  let fwid: fwid_payload_t = x509_get_fwid fwid in
  (* Prf *) lemma_serialize_fwid_size_exact fwid;

  let compositeDeviceID: compositeDeviceID_payload_t = {
    riot_version  = version;
    riot_deviceID = deviceIDPublicKeyInfo;
    riot_fwid     = fwid
  } in
  (* Prf *) lemma_serialize_compositeDeviceID_payload_size compositeDeviceID;
  (* Prf *) (**) lemma_serialize_asn1_integer_TLV_size compositeDeviceID.riot_version;

(* return *) compositeDeviceID
