module RIoT.X509.Extension

open ASN1.Spec
open ASN1.Low
open X509.BasicFields.Extension
include RIoT.X509.CompositeDeviceID

open FStar.Integers

#set-options "--z3rlimit 32 --fuel 0 --ifuel 0"
type riot_extension_payload_t: Type
= { x509_extID_riot      : x:datatype_of_asn1_type OID {x == OID_RIOT};
    x509_extCritical_riot: datatype_of_asn1_type BOOLEAN;
    x509_extValue_riot   : OCTET_STRING `inbound_envelop_tag_with_value_of`
                           (**) serialize_compositeDeviceID }

let synth_riot_extension_payload_t
  (x': x509_extension_t' OID_RIOT serialize_compositeDeviceID)
: GTot (riot_extension_payload_t)
= { x509_extID_riot       = fst (fst x');
    x509_extCritical_riot = snd (fst x');
    x509_extValue_riot    = snd x' }

let synth_riot_extension_payload_t_inverse
  (x: riot_extension_payload_t)
: Tot (x': x509_extension_t' OID_RIOT serialize_compositeDeviceID
           { x == synth_riot_extension_payload_t x' })
= ((x.x509_extID_riot,
    x.x509_extCritical_riot),
    x.x509_extValue_riot)

#set-options "--ifuel 1"
let parse_riot_extension_payload
: parser parse_x509_extension_kind riot_extension_payload_t
= parse_x509_extension
    OID_RIOT
    serialize_compositeDeviceID
    synth_riot_extension_payload_t
    ()

let serialize_riot_extension_payload
: serializer parse_riot_extension_payload
= serialize_x509_extension
    OID_RIOT
    serialize_compositeDeviceID
    synth_riot_extension_payload_t
    synth_riot_extension_payload_t_inverse
    ()

let lemma_serialize_riot_extension_payload_unfold
= lemma_serialize_x509_extension_unfold
    OID_RIOT
    serialize_compositeDeviceID
    synth_riot_extension_payload_t
    synth_riot_extension_payload_t_inverse
    ()

let lemma_serialize_riot_extension_payload_size
= lemma_serialize_x509_extension_size
    OID_RIOT
    serialize_compositeDeviceID
    synth_riot_extension_payload_t
    synth_riot_extension_payload_t_inverse
    ()

(*
 *
 *)

let riot_extension_t
= x509_extension_t_inbound
    OID_RIOT
    serialize_compositeDeviceID
    synth_riot_extension_payload_t
    synth_riot_extension_payload_t_inverse
    ()

let parse_riot_extension
: parser parse_x509_extension_sequence_TLV_kind riot_extension_t
= riot_extension_t
  `coerce_parser`
  parse_x509_extension_sequence_TLV
    OID_RIOT
    serialize_compositeDeviceID
    synth_riot_extension_payload_t
    synth_riot_extension_payload_t_inverse
    ()

let serialize_riot_extension
: serializer parse_riot_extension
= coerce_parser_serializer
  (* p2 *) parse_riot_extension
  (* s1 *) (serialize_x509_extension_sequence_TLV
              OID_RIOT
              serialize_compositeDeviceID
              synth_riot_extension_payload_t
              synth_riot_extension_payload_t_inverse
              ())
  (* prf*) ()

let lemma_serialize_riot_extension_unfold
= lemma_serialize_x509_extension_sequence_TLV_unfold
    OID_RIOT
    serialize_compositeDeviceID
    synth_riot_extension_payload_t
    synth_riot_extension_payload_t_inverse
    ()

let lemma_serialize_riot_extension_size
= lemma_serialize_x509_extension_sequence_TLV_size
    OID_RIOT
    serialize_compositeDeviceID
    synth_riot_extension_payload_t
    synth_riot_extension_payload_t_inverse
    ()

let length_of_riot_extension_payload
    (version: datatype_of_asn1_type INTEGER)
= length_of_asn1_primitive_TLV version + 109

let len_of_riot_extension_payload
    (version: datatype_of_asn1_type INTEGER
              { length_of_riot_extension_payload version
                <= asn1_value_length_max_of_type SEQUENCE })
: Tot (len: asn1_TLV_int32_of_type SEQUENCE
            { v len == length_of_riot_extension_payload version })
= len_of_asn1_primitive_TLV version + 109ul

#push-options "--z3rlimit 128 --fuel 0 --ifuel 2"
let lemma_serialize_riot_extension_payload_size_exact
  (x: riot_extension_t)
: Lemma (
  length_of_opaque_serialization serialize_riot_extension_payload x ==
  length_of_riot_extension_payload x.x509_extValue_riot.riot_version /\
  length_of_opaque_serialization serialize_riot_extension_payload x <= 115
)
= lemma_serialize_riot_extension_payload_size x;
  assert (length_of_asn1_primitive_TLV x.x509_extID_riot == 11);
  lemma_serialize_compositeDeviceID_size_exact x.x509_extValue_riot;
  assert (length_of_TLV OCTET_STRING (length_of_opaque_serialization serialize_compositeDeviceID x.x509_extValue_riot)
          == length_of_asn1_primitive_TLV x.x509_extValue_riot.riot_version + 95)

let length_of_riot_extension
    (version: datatype_of_asn1_type INTEGER)
= length_of_TLV SEQUENCE (length_of_riot_extension_payload version)

let len_of_riot_extension
    (version: datatype_of_asn1_type INTEGER
              { length_of_riot_extension version
                <= asn1_value_length_max_of_type SEQUENCE })
: Tot (len: asn1_TLV_int32_of_type SEQUENCE
            { v len == length_of_riot_extension version })
= len_of_TLV SEQUENCE (len_of_riot_extension_payload version)

let lemma_serialize_riot_extension_size_exact
  (x: riot_extension_t)
: Lemma (
  length_of_opaque_serialization serialize_riot_extension x ==
  length_of_riot_extension x.x509_extValue_riot.riot_version /\
  length_of_opaque_serialization serialize_riot_extension x <= 117
)
= lemma_serialize_riot_extension_size x;
  lemma_serialize_riot_extension_payload_size_exact x
#pop-options

(* low *)
open ASN1.Low

let serialize32_riot_extension_payload_backwards
: serializer32_backwards serialize_riot_extension_payload
= coerce_serializer32_backwards
  (* s2 *) (serialize_riot_extension_payload)
  (* s32*) (serialize32_x509_extension_backwards
              OID_RIOT
              serialize32_compositeDeviceID_backwards
              synth_riot_extension_payload_t
              synth_riot_extension_payload_t_inverse
              synth_riot_extension_payload_t_inverse
              ())
  (* prf*) ()

let serialize32_riot_extension_backwards
= coerce_serializer32_backwards
  (* s2 *) (serialize_riot_extension)
  (* s32*) (serialize32_x509_extension_sequence_TLV_backwards
              OID_RIOT
              serialize32_compositeDeviceID_backwards
              synth_riot_extension_payload_t
              synth_riot_extension_payload_t_inverse
              synth_riot_extension_payload_t_inverse
              ())
  (* prf*) ()

(* helpers *)
module B32 = FStar.Bytes

#restart-solver
#push-options "--z3rlimit 64 --fuel 0 --ifuel 0"
let x509_get_riot_extension
  (version: datatype_of_asn1_type INTEGER)
  (fwid: B32.lbytes32 32ul)
  (deviceIDPub: B32.lbytes32 32ul)
: Tot (riot_extension_t)
=
  let compositeDeviceID: compositeDeviceID_t = x509_get_compositeDeviceID version deviceIDPub fwid in
  (* Prf *) lemma_serialize_compositeDeviceID_size_exact compositeDeviceID;

  let riot_extension: riot_extension_payload_t = {
    x509_extID_riot       = OID_RIOT;
    x509_extCritical_riot = false;
    x509_extValue_riot    = compositeDeviceID
  } in
  (* Prf *) lemma_serialize_riot_extension_payload_unfold riot_extension;
  (* Prf *) lemma_serialize_riot_extension_payload_size   riot_extension;
  (* Prf *) (**) lemma_serialize_asn1_oid_TLV_size riot_extension.x509_extID_riot;
  (* Prf *) (**) lemma_serialize_asn1_boolean_TLV_size riot_extension.x509_extCritical_riot;

(*return*) riot_extension
#pop-options
