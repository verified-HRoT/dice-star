module RIoT.X509.AliasKeyCRT

open ASN1.Spec
open ASN1.Low
open X509
include RIoT.X509.Base
include RIoT.X509.FWID
include RIoT.X509.CompositeDeviceID
include RIoT.X509.Extension
open FStar.Integers

module B32 = FStar.Bytes

open LowParse.Spec.SeqBytes.Base
open LowParse.Spec.Bytes

#push-options "--query_stats --z3rlimit 32 --fuel 4 --ifuel 4"
type aliasKeyCRT_t (tbs_len: asn1_int32) = {
  aliasKeyCRT_tbs: B32.lbytes32 tbs_len;
  aliasKeyCRT_sig_alg: algorithmIdentifier_t_inbound ED25519;
  aliasKeyCRT_sig: x509_signature_t_inbound ED25519
}
#pop-options

let aliasKeyCRT_t' (tbs_len: asn1_int32) = (
  (B32.lbytes32 tbs_len `tuple2`
   algorithmIdentifier_t_inbound ED25519) `tuple2`
   x509_signature_t_inbound ED25519
)

let synth_aliasKeyCRT_t
  (tbs_len: asn1_int32)
  (x': aliasKeyCRT_t' tbs_len)
: GTot (aliasKeyCRT_t tbs_len)
= { aliasKeyCRT_tbs     = fst (fst x');
    aliasKeyCRT_sig_alg = snd (fst x');
    aliasKeyCRT_sig     = snd x' }

let synth_aliasKeyCRT_t'
  (tbs_len: asn1_int32)
  (x: aliasKeyCRT_t tbs_len)
: Tot (x': aliasKeyCRT_t' tbs_len { x == synth_aliasKeyCRT_t tbs_len x' })
= (x.aliasKeyCRT_tbs,
   x.aliasKeyCRT_sig_alg),
   x.aliasKeyCRT_sig

let parse_aliasKeyCRT
  (tbs_len: asn1_int32)
: parser _ (aliasKeyCRT_t tbs_len)
= parse_flbytes32 tbs_len
  `nondep_then`
  parse_algorithmIdentifier_sequence_TLV ED25519
  `nondep_then`
  parse_x509_signature_sequence_TLV ED25519
  `parse_synth`
  synth_aliasKeyCRT_t tbs_len

let serialize_aliasKeyCRT
  (tbs_len: asn1_int32)
: serializer (parse_aliasKeyCRT tbs_len)
= serialize_synth
  (* p1 *) (parse_flbytes32 tbs_len
            `nondep_then`
            parse_algorithmIdentifier_sequence_TLV ED25519
            `nondep_then`
            parse_x509_signature_sequence_TLV ED25519)
  (* f2 *) (synth_aliasKeyCRT_t tbs_len)
  (* s1 *) (serialize_flbytes32 tbs_len
            `serialize_nondep_then`
            serialize_algorithmIdentifier_sequence_TLV ED25519
            `serialize_nondep_then`
            serialize_x509_signature_sequence_TLV ED25519)
  (* g1 *) (synth_aliasKeyCRT_t' tbs_len)
  (* prf*) ()

let lemma_serialize_aliasKeyCRT_unfold
  (tbs_len: asn1_int32)
  (x: aliasKeyCRT_t tbs_len)
: Lemma (
  serialize_aliasKeyCRT tbs_len `serialize` x ==
 (serialize_flbytes32 tbs_len `serialize` x.aliasKeyCRT_tbs)
  `Seq.append`
 (serialize_algorithmIdentifier_sequence_TLV ED25519 `serialize` x.aliasKeyCRT_sig_alg)
  `Seq.append`
 (serialize_x509_signature_sequence_TLV ED25519 `serialize` x.aliasKeyCRT_sig)
)
= serialize_nondep_then_eq
  (* s1 *) (serialize_flbytes32 tbs_len)
  (* s2 *) (serialize_algorithmIdentifier_sequence_TLV ED25519)
  (* in *) (fst (synth_aliasKeyCRT_t' tbs_len x));
  serialize_nondep_then_eq
  (* s1 *) (serialize_flbytes32 tbs_len
            `serialize_nondep_then`
            serialize_algorithmIdentifier_sequence_TLV ED25519)
  (* s2 *) (serialize_x509_signature_sequence_TLV ED25519)
  (* in *) (synth_aliasKeyCRT_t' tbs_len x);
  serialize_synth_eq
  (* p1 *) (parse_flbytes32 tbs_len
            `nondep_then`
            parse_algorithmIdentifier_sequence_TLV ED25519
            `nondep_then`
            parse_x509_signature_sequence_TLV ED25519)
  (* f2 *) (synth_aliasKeyCRT_t tbs_len)
  (* s1 *) (serialize_flbytes32 tbs_len
            `serialize_nondep_then`
            serialize_algorithmIdentifier_sequence_TLV ED25519
            `serialize_nondep_then`
            serialize_x509_signature_sequence_TLV ED25519)
  (* g1 *) (synth_aliasKeyCRT_t' tbs_len)
  (* prf*) ()
  (* in *) x

#restart-solver
#push-options "--query_stats --z3rlimit 32" //--fuel 8 --ifuel 4"
let lemma_serialize_aliasKeyCRT_size
  (tbs_len: asn1_int32)
  (x: aliasKeyCRT_t tbs_len)
: Lemma (
  length_of_opaque_serialization (serialize_aliasKeyCRT tbs_len) x ==
  length_of_opaque_serialization (serialize_flbytes32 tbs_len) x.aliasKeyCRT_tbs +
  length_of_opaque_serialization (serialize_algorithmIdentifier_sequence_TLV ED25519) x.aliasKeyCRT_sig_alg +
  length_of_opaque_serialization (serialize_x509_signature_sequence_TLV ED25519) x.aliasKeyCRT_sig
)
= lemma_serialize_aliasKeyCRT_unfold tbs_len x
#pop-options

let aliasKeyCRT_t_inbound
  (tbs_len: asn1_int32)
= inbound_sequence_value_of (serialize_aliasKeyCRT tbs_len)

let parse_aliasKeyCRT_sequence_TLV
  (tbs_len: asn1_int32)
: parser (parse_asn1_envelop_tag_with_TLV_kind SEQUENCE) (aliasKeyCRT_t_inbound tbs_len)
= aliasKeyCRT_t_inbound tbs_len
  `coerce_parser`
  parse_asn1_sequence_TLV (serialize_aliasKeyCRT tbs_len)

let serialize_aliasKeyCRT_sequence_TLV
  (tbs_len: asn1_int32)
: serializer (parse_aliasKeyCRT_sequence_TLV tbs_len)
= coerce_parser_serializer
    (parse_aliasKeyCRT_sequence_TLV tbs_len)
    (serialize_asn1_sequence_TLV (serialize_aliasKeyCRT tbs_len))
    ()

let serialize_aliasKeyCRT_sequence_TLV_unfold
  (tbs_len: asn1_int32)
  (x: aliasKeyCRT_t_inbound tbs_len)
: Lemma ( prop_serialize_asn1_sequence_TLV_unfold (serialize_aliasKeyCRT tbs_len) x )
= lemma_serialize_asn1_sequence_TLV_unfold (serialize_aliasKeyCRT tbs_len) x

let serialize_aliasKeyCRT_sequence_TLV_size
  (tbs_len: asn1_int32)
  (x: aliasKeyCRT_t_inbound tbs_len)
: Lemma ( prop_serialize_asn1_sequence_TLV_size (serialize_aliasKeyCRT tbs_len) x )
= lemma_serialize_asn1_sequence_TLV_size (serialize_aliasKeyCRT tbs_len) x

(* low *)

let serialize32_aliasKeyCRT_backwards
  (tbs_len: asn1_int32)
: serializer32_backwards (serialize_aliasKeyCRT tbs_len)
= serialize32_synth_backwards
  (* s1 *) (serialize32_flbytes32_backwards tbs_len
            `serialize32_nondep_then_backwards`
            serialize32_algorithmIdentifier_sequence_TLV_backwards ED25519
            `serialize32_nondep_then_backwards`
            serialize32_x509_signature_sequence_TLV_backwards ED25519)
  (* f2 *) (synth_aliasKeyCRT_t  tbs_len)
  (* g1 *) (synth_aliasKeyCRT_t' tbs_len)
  (* g1'*) (synth_aliasKeyCRT_t' tbs_len)
  (* prf*) ()

let serialize32_aliasKeyCRT_sequence_TLV_backwards
  (tbs_len: asn1_int32)
: serializer32_backwards (serialize_aliasKeyCRT_sequence_TLV tbs_len)
= coerce_serializer32_backwards
    (serialize_aliasKeyCRT_sequence_TLV tbs_len)
    (serialize32_asn1_sequence_TLV_backwards
       (serialize32_aliasKeyCRT_backwards tbs_len))
    ()

