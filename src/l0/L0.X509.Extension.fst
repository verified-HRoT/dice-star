module L0.X509.Extension

open ASN1.Spec
open ASN1.Low
open X509.BasicFields.Extension
include L0.X509.CompositeDeviceID

open FStar.Integers

#set-options "--z3rlimit 32 --fuel 0 --ifuel 0 --using_facts_from '* -FStar.Tactics -FStar.Reflection'"

type l0_extension_payload_t: Type
= { x509_extID_l0      : x:datatype_of_asn1_type OID {x == OID_RIOT};
    x509_extCritical_l0: datatype_of_asn1_type BOOLEAN;
    x509_extValue_l0   : OCTET_STRING `inbound_envelop_tag_with_value_of`
                           (**) serialize_compositeDeviceID }

let synth_l0_extension_payload_t
  (x': x509_extension_t' OID_RIOT serialize_compositeDeviceID)
: GTot (l0_extension_payload_t)
= { x509_extID_l0       = fst (fst x');
    x509_extCritical_l0 = snd (fst x');
    x509_extValue_l0    = snd x' }

inline_for_extraction noextract
let synth_l0_extension_payload_t_inverse
  (x: l0_extension_payload_t)
: Tot (x': x509_extension_t' OID_RIOT serialize_compositeDeviceID
           { x == synth_l0_extension_payload_t x' })
= ((x.x509_extID_l0,
    x.x509_extCritical_l0),
    x.x509_extValue_l0)

#set-options "--ifuel 1"
let parse_l0_extension_payload
: parser parse_x509_extension_kind l0_extension_payload_t
= parse_x509_extension
    OID_RIOT
    serialize_compositeDeviceID
    synth_l0_extension_payload_t
    ()

let serialize_l0_extension_payload
: serializer parse_l0_extension_payload
= serialize_x509_extension
    OID_RIOT
    serialize_compositeDeviceID
    synth_l0_extension_payload_t
    synth_l0_extension_payload_t_inverse
    ()

let lemma_serialize_l0_extension_payload_unfold
= lemma_serialize_x509_extension_unfold
    OID_RIOT
    serialize_compositeDeviceID
    synth_l0_extension_payload_t
    synth_l0_extension_payload_t_inverse
    ()

let lemma_serialize_l0_extension_payload_size
= lemma_serialize_x509_extension_size
    OID_RIOT
    serialize_compositeDeviceID
    synth_l0_extension_payload_t
    synth_l0_extension_payload_t_inverse
    ()

(*
 *
 *)

let l0_extension_t
= x509_extension_t_inbound
    OID_RIOT
    serialize_compositeDeviceID
    synth_l0_extension_payload_t
    synth_l0_extension_payload_t_inverse
    ()

let parse_l0_extension
: parser parse_x509_extension_sequence_TLV_kind l0_extension_t
= l0_extension_t
  `coerce_parser`
  parse_x509_extension_sequence_TLV
    OID_RIOT
    serialize_compositeDeviceID
    synth_l0_extension_payload_t
    synth_l0_extension_payload_t_inverse
    ()

let serialize_l0_extension
: serializer parse_l0_extension
= coerce_parser_serializer
  (* p2 *) parse_l0_extension
  (* s1 *) (serialize_x509_extension_sequence_TLV
              OID_RIOT
              serialize_compositeDeviceID
              synth_l0_extension_payload_t
              synth_l0_extension_payload_t_inverse
              ())
  (* prf*) ()

let lemma_serialize_l0_extension_unfold
= lemma_serialize_x509_extension_sequence_TLV_unfold
    OID_RIOT
    serialize_compositeDeviceID
    synth_l0_extension_payload_t
    synth_l0_extension_payload_t_inverse
    ()

let lemma_serialize_l0_extension_size
= lemma_serialize_x509_extension_sequence_TLV_size
    OID_RIOT
    serialize_compositeDeviceID
    synth_l0_extension_payload_t
    synth_l0_extension_payload_t_inverse
    ()

let length_of_l0_extension_payload
    (version: datatype_of_asn1_type INTEGER)
= length_of_asn1_primitive_TLV version + 110

let len_of_l0_extension_payload
    (version: datatype_of_asn1_type INTEGER
              { length_of_l0_extension_payload version
                <= asn1_value_length_max_of_type SEQUENCE })
: Tot (len: asn1_TLV_int32_of_type SEQUENCE
            { v len == length_of_l0_extension_payload version })
= len_of_asn1_primitive_TLV version + 110ul

#push-options "--z3rlimit 128 --fuel 0 --ifuel 2"
let lemma_serialize_l0_extension_payload_size_exact
  (x: l0_extension_t)
: Lemma (
  length_of_opaque_serialization serialize_l0_extension_payload x ==
  length_of_l0_extension_payload x.x509_extValue_l0.l0_version /\
  length_of_opaque_serialization serialize_l0_extension_payload x <= 116
)
= lemma_serialize_l0_extension_payload_size x;
  assert (length_of_asn1_primitive_TLV x.x509_extID_l0 == 12);
  lemma_serialize_compositeDeviceID_size_exact x.x509_extValue_l0;
  assert (length_of_TLV OCTET_STRING (length_of_opaque_serialization serialize_compositeDeviceID x.x509_extValue_l0)
          == length_of_asn1_primitive_TLV x.x509_extValue_l0.l0_version + 95)

let length_of_l0_extension
    (version: datatype_of_asn1_type INTEGER)
= L0.X509.LengthUtils.lemma_length_of_l0_extension version;
  length_of_TLV SEQUENCE (length_of_l0_extension_payload version)

noextract inline_for_extraction unfold
[@@ "opaque_to_smt"]
let len_of_l0_extension_max ()
: Tot (asn1_TLV_int32_of_type SEQUENCE)
= 118ul

let len_of_l0_extension
    (version: datatype_of_asn1_type INTEGER)
: Tot (len: asn1_TLV_int32_of_type SEQUENCE
            { v len == length_of_l0_extension version })
= L0.X509.LengthUtils.lemma_length_of_l0_extension version;
  len_of_TLV SEQUENCE (len_of_l0_extension_payload version)

let lemma_serialize_l0_extension_size_exact
  (x: l0_extension_t)
: Lemma (
  length_of_opaque_serialization serialize_l0_extension x ==
  length_of_l0_extension x.x509_extValue_l0.l0_version /\
  length_of_opaque_serialization serialize_l0_extension x
  <= v (len_of_l0_extension_max ())
)
= lemma_serialize_l0_extension_size x;
  lemma_serialize_l0_extension_payload_size_exact x;
  L0.X509.LengthUtils.lemma_length_of_l0_extension_l0_version
    x.x509_extValue_l0.l0_version
#pop-options

(* low *)
open ASN1.Low

let serialize32_l0_extension_payload_backwards
: serializer32_backwards serialize_l0_extension_payload
= coerce_serializer32_backwards
  (* s2 *) (serialize_l0_extension_payload)
  (* s32*) (serialize32_x509_extension_backwards
              OID_RIOT
              serialize32_compositeDeviceID_backwards
              synth_l0_extension_payload_t
              synth_l0_extension_payload_t_inverse
              synth_l0_extension_payload_t_inverse
              ())
  (* prf*) ()

let serialize32_l0_extension_backwards
= coerce_serializer32_backwards
  (* s2 *) (serialize_l0_extension)
  (* s32*) (serialize32_x509_extension_sequence_TLV_backwards
              OID_RIOT
              serialize32_compositeDeviceID_backwards
              synth_l0_extension_payload_t
              synth_l0_extension_payload_t_inverse
              synth_l0_extension_payload_t_inverse
              ())
  (* prf*) ()

(* helpers *)
module B32 = FStar.Bytes

#restart-solver
#push-options "--z3rlimit 64 --fuel 0 --ifuel 0"
let x509_get_l0_extension
  (version: datatype_of_asn1_type INTEGER)
  (fwid: B32.lbytes32 32ul)
  (deviceIDPub: B32.lbytes32 32ul)
: Tot (l0_extension_t)
=
  let compositeDeviceID: compositeDeviceID_t = x509_get_compositeDeviceID version deviceIDPub fwid in
  (* Prf *) lemma_serialize_compositeDeviceID_size_exact compositeDeviceID;

  let l0_extension: l0_extension_payload_t = {
    x509_extID_l0       = OID_RIOT;
    x509_extCritical_l0 = false;
    x509_extValue_l0    = compositeDeviceID
  } in
  (* Prf *) lemma_serialize_l0_extension_payload_unfold l0_extension;
  (* Prf *) lemma_serialize_l0_extension_payload_size   l0_extension;
  (* Prf *) (**) lemma_serialize_asn1_oid_TLV_size l0_extension.x509_extID_l0;
  (* Prf *) (**) lemma_serialize_asn1_boolean_TLV_size l0_extension.x509_extCritical_l0;

(*return*) l0_extension
#pop-options
