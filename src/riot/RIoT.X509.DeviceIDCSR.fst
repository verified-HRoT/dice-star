module RIoT.X509.DeviceIDCSR

open ASN1.Spec
open ASN1.Low
open X509
open RIoT.X509.DeviceIDCRI
open FStar.Integers

module B32 = FStar.Bytes

#set-options "--z3rlimit 32 --fuel 0 --ifuel 0"

type deviceIDCSR_payload_t (cri_len: asn1_int32) = {
  deviceIDCSR_cri: B32.lbytes32 cri_len;
  deviceIDCSR_sig_alg: algorithmIdentifier_t;
  deviceIDCSR_sig: x509_signature_t
}

let deviceIDCSR_payload_t' (cri_len: asn1_int32) = (
  (B32.lbytes32 cri_len `tuple2`
   algorithmIdentifier_t) `tuple2`
   x509_signature_t
)

let synth_deviceIDCSR_payload_t
  (cri_len: asn1_int32)
  (x': deviceIDCSR_payload_t' cri_len)
: GTot (deviceIDCSR_payload_t cri_len)
= { deviceIDCSR_cri     = fst (fst x');
    deviceIDCSR_sig_alg = snd (fst x');
    deviceIDCSR_sig     = snd x' }

let synth_deviceIDCSR_payload_t'
  (cri_len: asn1_int32)
  (x: deviceIDCSR_payload_t cri_len)
: Tot (x': deviceIDCSR_payload_t' cri_len { x == synth_deviceIDCSR_payload_t cri_len x' })
= (x.deviceIDCSR_cri,
   x.deviceIDCSR_sig_alg),
   x.deviceIDCSR_sig

let parse_deviceIDCSR_payload
  (cri_len: asn1_int32)
: parser _ (deviceIDCSR_payload_t cri_len)
= parse_flbytes32 cri_len
  `nondep_then`
  parse_algorithmIdentifier
  `nondep_then`
  parse_x509_signature
  `parse_synth`
  synth_deviceIDCSR_payload_t cri_len

let serialize_deviceIDCSR_payload
  (cri_len: asn1_int32)
: serializer (parse_deviceIDCSR_payload cri_len)
= serialize_synth
  (* p1 *) (parse_flbytes32 cri_len
            `nondep_then`
            parse_algorithmIdentifier
            `nondep_then`
            parse_x509_signature)
  (* f2 *) (synth_deviceIDCSR_payload_t cri_len)
  (* s1 *) (serialize_flbytes32 cri_len
            `serialize_nondep_then`
            serialize_algorithmIdentifier
            `serialize_nondep_then`
            serialize_x509_signature)
  (* g1 *) (synth_deviceIDCSR_payload_t' cri_len)
  (* prf*) ()

let lemma_serialize_deviceIDCSR_payload_unfold
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
= serialize_nondep_then_eq
  (* s1 *) (serialize_flbytes32 cri_len)
  (* s2 *) (serialize_algorithmIdentifier)
  (* in *) (fst (synth_deviceIDCSR_payload_t' cri_len x));
  serialize_nondep_then_eq
  (* s1 *) (serialize_flbytes32 cri_len
            `serialize_nondep_then`
            serialize_algorithmIdentifier)
  (* s2 *) (serialize_x509_signature)
  (* in *) (synth_deviceIDCSR_payload_t' cri_len x);
  serialize_synth_eq
  (* p1 *) (parse_flbytes32 cri_len
            `nondep_then`
            parse_algorithmIdentifier
            `nondep_then`
            parse_x509_signature)
  (* f2 *) (synth_deviceIDCSR_payload_t cri_len)
  (* s1 *) (serialize_flbytes32 cri_len
            `serialize_nondep_then`
            serialize_algorithmIdentifier
            `serialize_nondep_then`
            serialize_x509_signature)
  (* g1 *) (synth_deviceIDCSR_payload_t' cri_len)
  (* prf*) ()
  (* in *) x

let length_of_deviceIDCSR_payload
  (cri_len: asn1_int32)
= v cri_len + 74

#push-options "--z3rlimit 64"
let len_of_deviceIDCSR_payload
  (cri_len: asn1_int32
            { length_of_deviceIDCSR_payload cri_len
              <= asn1_value_length_max_of_type SEQUENCE })
: Tot (len: asn1_TLV_int32_of_type SEQUENCE
            { v len == length_of_deviceIDCSR_payload cri_len })
= cri_len + 74ul
#pop-options

#restart-solver
#push-options "--z3rlimit 128 --fuel 0 --ifuel 0"
let lemma_serialize_deviceIDCSR_payload_size
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
= lemma_serialize_deviceIDCSR_payload_unfold cri_len x;
  (**) lemma_serialize_algorithmIdentifier_size_exact x.deviceIDCSR_sig_alg;
  (**) lemma_serialize_x509_signature_size      x.deviceIDCSR_sig
#pop-options


(* SEQUENCE TLV*)
let deviceIDCSR_t
  (cri_len: asn1_int32)
= inbound_sequence_value_of (serialize_deviceIDCSR_payload cri_len)

let parse_deviceIDCSR
  (cri_len: asn1_int32)
: parser (parse_asn1_envelop_tag_with_TLV_kind SEQUENCE) (deviceIDCSR_t cri_len)
= deviceIDCSR_t cri_len
  `coerce_parser`
  parse_asn1_sequence_TLV (serialize_deviceIDCSR_payload cri_len)

let serialize_deviceIDCSR
  (cri_len: asn1_int32)
: serializer (parse_deviceIDCSR cri_len)
= coerce_parser_serializer
    (parse_deviceIDCSR cri_len)
    (serialize_asn1_sequence_TLV (serialize_deviceIDCSR_payload cri_len))
    ()

let lemma_serialize_deviceIDCSR_unfold
  (cri_len: asn1_int32)
  (x: deviceIDCSR_t cri_len)
: Lemma ( predicate_serialize_asn1_sequence_TLV_unfold (serialize_deviceIDCSR_payload cri_len) x )
= lemma_serialize_asn1_sequence_TLV_unfold (serialize_deviceIDCSR_payload cri_len) x

let lemma_serialize_deviceIDCSR_size
  (cri_len: asn1_int32)
  (x: deviceIDCSR_t cri_len)
: Lemma ( predicate_serialize_asn1_sequence_TLV_size (serialize_deviceIDCSR_payload cri_len) x )
= lemma_serialize_asn1_sequence_TLV_size (serialize_deviceIDCSR_payload cri_len) x

let valid_deviceIDCSR_ingredients
  (cri_len: asn1_int32)
:Type0
= length_of_deviceIDCSR_payload cri_len <= asn1_value_length_max_of_type SEQUENCE

#push-options "--z3rlimit 64 --fuel 0 --ifuel 0"
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
#pop-options

#push-options "--z3rlimit 64 --fuel 0 --ifuel 0"
let lemma_serialize_deviceIDCSR_size_exact
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
= lemma_serialize_deviceIDCSR_size cri_len x;
  (**) lemma_serialize_deviceIDCSR_payload_size cri_len x
#pop-options


(* low *)

let serialize32_deviceIDCSR_payload_backwards
  (cri_len: asn1_int32)
: serializer32_backwards (serialize_deviceIDCSR_payload cri_len)
= serialize32_synth_backwards
  (* s1 *) (serialize32_flbytes32_backwards cri_len
            `serialize32_nondep_then_backwards`
            serialize32_algorithmIdentifier_backwards
            `serialize32_nondep_then_backwards`
            serialize32_x509_signature_backwards)
  (* f2 *) (synth_deviceIDCSR_payload_t  cri_len)
  (* g1 *) (synth_deviceIDCSR_payload_t' cri_len)
  (* g1'*) (synth_deviceIDCSR_payload_t' cri_len)
  (* prf*) ()

let serialize32_deviceIDCSR_backwards
  (cri_len: asn1_int32)
: serializer32_backwards (serialize_deviceIDCSR cri_len)
= coerce_serializer32_backwards
    (serialize_deviceIDCSR cri_len)
    (serialize32_asn1_sequence_TLV_backwards
       (serialize32_deviceIDCSR_payload_backwards cri_len))
    ()

#restart-solver
#push-options "--z3rlimit 32 --fuel 0 --ifuel 0"
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
