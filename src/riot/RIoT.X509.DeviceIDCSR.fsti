module RIoT.X509.DeviceIDCSR

open ASN1.Spec
open ASN1.Low
open X509
open RIoT.X509.DeviceIDCRI
open FStar.Integers

module B32 = FStar.Bytes

#set-options "--z3rlimit 128 --fuel 0 --ifuel 0 --using_facts_from '* -FStar.Tactics -FStar.Reflection'"

#set-options "--__temp_no_proj RIoT.X509.DeviceIDCSR"

val decl : unit

noeq
type deviceIDCSR_payload_t (cri_len: asn1_int32) = {
  deviceIDCSR_cri: B32.lbytes32 cri_len;
  deviceIDCSR_sig_alg: algorithmIdentifier_t;
  deviceIDCSR_sig: x509_signature_t
}

inline_for_extraction noextract
let parse_deviceIDCSR_payload_kind
  (cri_len: asn1_int32)
: parser_kind
= total_constant_size_parser_kind (v cri_len)
  `and_then_kind`
  parse_asn1_envelop_tag_with_TLV_kind SEQUENCE
  `and_then_kind`
  parse_x509_signature_kind

noextract
val parse_deviceIDCSR_payload
  (cri_len: asn1_int32)
: parser
  (parse_deviceIDCSR_payload_kind cri_len)
  (deviceIDCSR_payload_t cri_len)

noextract
val serialize_deviceIDCSR_payload
  (cri_len: asn1_int32)
: serializer (parse_deviceIDCSR_payload cri_len)

val lemma_serialize_deviceIDCSR_payload_unfold
  (cri_len: asn1_int32)
  (x: deviceIDCSR_payload_t cri_len)
: Lemma (
  serialize_deviceIDCSR_payload cri_len `serialize` x ==
 (serialize_flbytes32 cri_len `serialize` x.deviceIDCSR_cri)
  `Seq.append`
 (serialize_algorithmIdentifier `serialize` x.deviceIDCSR_sig_alg)
  `Seq.append`
 (serialize_x509_signature `serialize` x.deviceIDCSR_sig)
)

let length_of_deviceIDCSR_payload
  (cri_len: asn1_int32)
: GTot (nat)
= v cri_len + 74

let len_of_deviceIDCSR_payload
  (cri_len: asn1_int32
            { length_of_deviceIDCSR_payload cri_len
              <= asn1_value_length_max_of_type SEQUENCE })
: Tot (len: asn1_TLV_int32_of_type SEQUENCE
            { v len == length_of_deviceIDCSR_payload cri_len })
= cri_len + 74ul

val lemma_serialize_deviceIDCSR_payload_size
  (cri_len: asn1_int32)
  (x: deviceIDCSR_payload_t cri_len)
: Lemma (
  (* unfold *)
  length_of_opaque_serialization (serialize_deviceIDCSR_payload cri_len) x ==
  length_of_opaque_serialization (serialize_flbytes32 cri_len) x.deviceIDCSR_cri +
  length_of_opaque_serialization (serialize_algorithmIdentifier) x.deviceIDCSR_sig_alg +
  length_of_opaque_serialization (serialize_x509_signature) x.deviceIDCSR_sig /\
  (* exact size *)
  length_of_opaque_serialization (serialize_deviceIDCSR_payload cri_len) x
  == length_of_deviceIDCSR_payload cri_len
)

(* SEQUENCE TLV*)
let deviceIDCSR_t
  (cri_len: asn1_int32)
= inbound_sequence_value_of (serialize_deviceIDCSR_payload cri_len)

noextract
let parse_deviceIDCSR
  (cri_len: asn1_int32)
: parser (parse_asn1_envelop_tag_with_TLV_kind SEQUENCE) (deviceIDCSR_t cri_len)
= deviceIDCSR_t cri_len
  `coerce_parser`
  parse_asn1_sequence_TLV (serialize_deviceIDCSR_payload cri_len)

noextract
let serialize_deviceIDCSR
  (cri_len: asn1_int32)
: serializer (parse_deviceIDCSR cri_len)
= coerce_parser_serializer
    (parse_deviceIDCSR cri_len)
    (serialize_asn1_sequence_TLV (serialize_deviceIDCSR_payload cri_len))
    ()

val lemma_serialize_deviceIDCSR_unfold
  (cri_len: asn1_int32)
  (x: deviceIDCSR_t cri_len)
: Lemma ( predicate_serialize_asn1_sequence_TLV_unfold (serialize_deviceIDCSR_payload cri_len) x )

val lemma_serialize_deviceIDCSR_size
  (cri_len: asn1_int32)
  (x: deviceIDCSR_t cri_len)
: Lemma ( predicate_serialize_asn1_sequence_TLV_size (serialize_deviceIDCSR_payload cri_len) x )

let valid_deviceIDCSR_ingredients
  (cri_len: asn1_int32)
:Type0
= length_of_deviceIDCSR_payload cri_len <= asn1_value_length_max_of_type SEQUENCE

let length_of_deviceIDCSR
  (cri_len: asn1_int32
            { valid_deviceIDCSR_ingredients cri_len })
: GTot (asn1_TLV_length_of_type SEQUENCE)
= length_of_TLV
    (SEQUENCE)
    (length_of_deviceIDCSR_payload cri_len)

let len_of_deviceIDCSR
  (cri_len: asn1_int32
            { valid_deviceIDCSR_ingredients cri_len })
: Tot (len: asn1_TLV_int32_of_type SEQUENCE
            { v len == length_of_deviceIDCSR cri_len })
= len_of_TLV
    (SEQUENCE)
    (len_of_deviceIDCSR_payload cri_len)

val lemma_serialize_deviceIDCSR_size_exact
  (cri_len: asn1_int32)
  (x: deviceIDCSR_t cri_len)
: Lemma (
  let _ = lemma_serialize_deviceIDCSR_payload_size cri_len x in
  (* exact size *)
  length_of_opaque_serialization (serialize_deviceIDCSR cri_len) x
  == length_of_deviceIDCSR cri_len /\
  (* upper bound *)
  length_of_opaque_serialization (serialize_deviceIDCSR cri_len) x
  <= v cri_len + 84
)


(* low *)

val serialize32_deviceIDCSR_payload_backwards
  (cri_len: asn1_int32)
: serializer32_backwards (serialize_deviceIDCSR_payload cri_len)

val serialize32_deviceIDCSR_backwards
  (cri_len: asn1_int32)
: serializer32_backwards (serialize_deviceIDCSR cri_len)

let x509_get_deviceIDCSR
  (cri_len: asn1_int32
            { valid_deviceIDCSR_ingredients cri_len })
  (deviceIDCSR_cri: B32.lbytes32 cri_len)
  (signature32: x509_signature_raw_t) // B32.lbytes32 64ul
: Tot (deviceIDCSR_t cri_len)
=
  let deviceIDCSR_sig_alg = x509_get_algorithmIdentifier () in
  (* Prf *) lemma_serialize_algorithmIdentifier_size_exact deviceIDCSR_sig_alg;

  let deviceIDCSR_sig = x509_get_signature signature32 in
  (* Prf *) lemma_serialize_x509_signature_size deviceIDCSR_sig;

  let deviceIDCSR: deviceIDCSR_payload_t cri_len = {
    deviceIDCSR_cri     = deviceIDCSR_cri;
    deviceIDCSR_sig_alg = deviceIDCSR_sig_alg;
    deviceIDCSR_sig     = deviceIDCSR_sig
  } in
  (* Prf *) lemma_serialize_deviceIDCSR_payload_unfold cri_len deviceIDCSR;
  (* Prf *) lemma_serialize_deviceIDCSR_payload_size   cri_len deviceIDCSR;
  (* Prf *) (**) lemma_serialize_flbytes32_size cri_len deviceIDCSR.deviceIDCSR_cri;

(* return *) deviceIDCSR
