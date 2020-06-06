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

unfold
let parse_riot_extension
: parser parse_x509_extension_kind riot_extension_t
= parse_x509_extension OID_RIOT serialize_compositeDeviceID_sequence_TLV

unfold
let serialize_riot_extension
: serializer parse_riot_extension
= serialize_x509_extension OID_RIOT serialize_compositeDeviceID_sequence_TLV

#set-options "--z3rlimit 8"
let _ = assert (length_of_oid OID_EC_GRP_SECP256R1 == 6)
let _ = assert (length_of_asn1_primitive_TLV (Mkbit_string_t 33ul 0ul (magic())) == 35)

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


#set-options "--z3rlimit 8"
let _ = assert (length_of_oid OID_EC_GRP_SECP256R1 == 6)
let _ = assert (length_of_asn1_primitive_TLV (Mkbit_string_t 33ul 0ul (magic())) == 35)
