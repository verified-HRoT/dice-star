module RIoT.X509.Extension

open ASN1.Spec
open X509.BasicFields.Extension
open RIoT.X509.CompositeDeviceID

// #set-options "--z3rlimit 8"
let _ = assert (length_of_oid OID_EC_GRP_SECP256R1 == 6)
let _ = assert (length_of_asn1_primitive_TLV (Mkbit_string_t 33ul 0ul (magic())) == 35)

unfold
let riot_extension_t
= x509_extension_t OID_RIOT serialize_compositeDeviceID_sequence_TLV

// #set-options "--query_stats --z3rlimit 32 --fuel 8 --ifuel 8"
// let _ = assert (length_of_oid OID_EC_GRP_SECP256R1 == 6)
// let _ = assert_norm (length_of_asn1_primitive_TLV (Mkbit_string_t 33ul 0ul (magic())) == 35)

unfold
let parse_riot_extension
: parser parse_x509_extension_kind riot_extension_t
= parse_x509_extension OID_RIOT serialize_compositeDeviceID_sequence_TLV

unfold
let serialize_riot_extension
: serializer parse_riot_extension
= serialize_x509_extension OID_RIOT serialize_compositeDeviceID_sequence_TLV

let lemma_serialize_riot_extension_unfold
= lemma_serialize_x509_extension_unfold OID_RIOT serialize_compositeDeviceID_sequence_TLV

let lemma_serialize_riot_extension_size
= lemma_serialize_x509_extension_size OID_RIOT serialize_compositeDeviceID_sequence_TLV


let riot_extension_t_inbound
= x509_extension_t_inbound OID_RIOT serialize_compositeDeviceID_sequence_TLV

let parse_riot_extension_sequence_TLV
: parser parse_x509_extension_sequence_TLV_kind riot_extension_t_inbound
= assert (x509_extension_t_inbound OID_RIOT serialize_compositeDeviceID_sequence_TLV == riot_extension_t_inbound);
  riot_extension_t_inbound
  `coerce_parser`
  parse_x509_extension_sequence_TLV OID_RIOT serialize_compositeDeviceID_sequence_TLV

let serialize_riot_extension_sequence_TLV
: serializer parse_riot_extension_sequence_TLV
= coerce_parser_serializer
  (* p2 *) parse_riot_extension_sequence_TLV
  (* s1 *) (serialize_x509_extension_sequence_TLV OID_RIOT serialize_compositeDeviceID_sequence_TLV)
  (* prf*) ()

let lemma_serialize_riot_extension_sequence_TLV_unfold
= lemma_serialize_x509_extension_sequence_TLV_unfold OID_RIOT serialize_compositeDeviceID_sequence_TLV

let lemma_serialize_riot_extension_sequence_TLV_size
= lemma_serialize_x509_extension_sequence_TLV_size OID_RIOT serialize_compositeDeviceID_sequence_TLV

#push-options "--query_stats --z3rlimit 64 --fuel 4 --ifuel 4"
let lemma_serialize_riot_extension_size_exact
  (x: riot_extension_t_inbound)
: Lemma (
  length_of_opaque_serialization serialize_riot_extension x ==
  length_of_asn1_primitive_TLV x.x509_extValue.riot_version + 109 /\
  length_of_opaque_serialization serialize_riot_extension x <= 115
)
= lemma_serialize_riot_extension_size x;
  assert (length_of_asn1_primitive_TLV x.x509_extID == 11);
  lemma_serialize_compositeDeviceID_sequence_TLV_size_exact x.x509_extValue;
  assert (length_of_TLV OCTET_STRING (length_of_opaque_serialization serialize_compositeDeviceID_sequence_TLV x.x509_extValue)
          == length_of_asn1_primitive_TLV x.x509_extValue.riot_version + 95)

let lemma_serialize_riot_extension_sequence_TLV_size_exact
  (x: riot_extension_t_inbound)
: Lemma (
  length_of_opaque_serialization serialize_riot_extension_sequence_TLV x ==
  length_of_asn1_primitive_TLV x.x509_extValue.riot_version + 111 /\
  length_of_opaque_serialization serialize_riot_extension x <= 117
)
= lemma_serialize_riot_extension_sequence_TLV_size x;
  lemma_serialize_riot_extension_size_exact x
#pop-options

(* low *)
open ASN1.Low

let serialize32_riot_extension_backwards
: serializer32_backwards serialize_riot_extension
= coerce_serializer32_backwards
  (* s2 *) (serialize_riot_extension)
  (* s32*) (serialize32_x509_extension_backwards
              OID_RIOT
              serialize32_compositeDeviceID_sequence_TLV_backwards)
  (* prf*) ()

let serialize32_riot_extension_sequence_TLV_backwards
= coerce_serializer32_backwards
  (* s2 *) (serialize_riot_extension_sequence_TLV)
  (* s32*) (serialize32_x509_extension_sequence_TLV_backwards
              OID_RIOT
              serialize32_compositeDeviceID_sequence_TLV_backwards)
  (* prf*) ()


// #set-options "--z3rlimit 8"
// let _ = assert (length_of_oid OID_EC_GRP_SECP256R1 == 6)
// let _ = assert (length_of_asn1_primitive_TLV (Mkbit_string_t 33ul 0ul (magic())) == 35)

(* helpers *)
module B32 = FStar.Bytes

#restart-solver
#push-options "--query_stats --z3rlimit 64 --fuel 8 --ifuel 4"
let x509_get_riot_extension
  (version: datatype_of_asn1_type INTEGER)
  (deviceKeyPub: B32.lbytes32 32ul)
  (fwid: B32.lbytes32 32ul)
: Tot (riot_extension_t_inbound)
=
  let compositeDeviceID: compositeDeviceID_t_inbound = x509_get_compositeDeviceID version deviceKeyPub fwid in
  (* Prf *) lemma_serialize_compositeDeviceID_sequence_TLV_size_exact compositeDeviceID;

  let riot_extension: riot_extension_t = {
    x509_extID       = OID_RIOT;
    x509_extCritical = false;
    x509_extValue    = compositeDeviceID
  } in
  (* Prf *) lemma_serialize_riot_extension_unfold riot_extension;
  (* Prf *) lemma_serialize_riot_extension_size   riot_extension;
  (* Prf *) (**) lemma_serialize_asn1_oid_TLV_size riot_extension.x509_extID;
  (* Prf *) (**) lemma_serialize_asn1_boolean_TLV_size riot_extension.x509_extCritical;

(*return*) riot_extension
#pop-options
