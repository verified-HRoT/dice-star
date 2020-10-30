module RIoT.X509.DeviceIDCSR

open ASN1.Spec
open ASN1.Low
open X509
open RIoT.X509.DeviceIDCRI
open FStar.Integers

module B32 = FStar.Bytes

#set-options "--z3rlimit 128 --fuel 0 --ifuel 0 --using_facts_from '* -FStar.Tactics -FStar.Reflection'"

#set-options "--__temp_no_proj RIoT.X509.DeviceIDCSR"

let decl = ()

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

inline_for_extraction noextract
let synth_deviceIDCSR_payload_t'
  (cri_len: asn1_int32)
  (x: deviceIDCSR_payload_t cri_len)
: Tot (x': deviceIDCSR_payload_t' cri_len { x == synth_deviceIDCSR_payload_t cri_len x' })
= (x.deviceIDCSR_cri,
   x.deviceIDCSR_sig_alg),
   x.deviceIDCSR_sig

let parse_deviceIDCSR_payload cri_len
= parse_flbytes32 cri_len
  `nondep_then`
  parse_algorithmIdentifier
  `nondep_then`
  parse_x509_signature
  `parse_synth`
  synth_deviceIDCSR_payload_t cri_len

let serialize_deviceIDCSR_payload cri_len
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

let lemma_serialize_deviceIDCSR_payload_unfold cri_len x
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

let lemma_serialize_deviceIDCSR_payload_size cri_len x
= lemma_serialize_deviceIDCSR_payload_unfold cri_len x;
  (**) lemma_serialize_algorithmIdentifier_size_exact x.deviceIDCSR_sig_alg;
  (**) lemma_serialize_x509_signature_size      x.deviceIDCSR_sig

let lemma_serialize_deviceIDCSR_unfold cri_len x
= lemma_serialize_asn1_sequence_TLV_unfold (serialize_deviceIDCSR_payload cri_len) x

let lemma_serialize_deviceIDCSR_size cri_len x
= lemma_serialize_asn1_sequence_TLV_size (serialize_deviceIDCSR_payload cri_len) x

let lemma_serialize_deviceIDCSR_size_exact cri_len x
= lemma_serialize_deviceIDCSR_size cri_len x;
  (**) lemma_serialize_deviceIDCSR_payload_size cri_len x


(* low *)

let serialize32_deviceIDCSR_payload_backwards cri_len
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

let serialize32_deviceIDCSR_backwards cri_len
= coerce_serializer32_backwards
    (serialize_deviceIDCSR cri_len)
    (serialize32_asn1_sequence_TLV_backwards
       (serialize32_deviceIDCSR_payload_backwards cri_len))
    ()
