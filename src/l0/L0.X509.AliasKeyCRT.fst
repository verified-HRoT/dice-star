module L0.X509.AliasKeyCRT

open ASN1.Spec
open ASN1.Low
open X509
include RIoT.X509.Base
include RIoT.X509.FWID
include RIoT.X509.CompositeDeviceID
include RIoT.X509.Extension
open FStar.Integers

module B32 = FStar.Bytes

#set-options "--z3rlimit 64 --fuel 0 --ifuel 0 --using_facts_from '* -FStar.Tactics -FStar.Reflection'"

#set-options "--__temp_no_proj RIoT.X509.AliasKeyCRT"

let decl = ()

let aliasKeyCRT_payload_t' (tbs_len: asn1_int32) = (
  (B32.lbytes32 tbs_len `tuple2`
   algorithmIdentifier_t) `tuple2`
   x509_signature_t
)

let synth_aliasKeyCRT_payload_t
  (tbs_len: asn1_int32)
  (x': aliasKeyCRT_payload_t' tbs_len)
: GTot (aliasKeyCRT_payload_t tbs_len)
= { aliasKeyCRT_tbs     = fst (fst x');
    aliasKeyCRT_sig_alg = snd (fst x');
    aliasKeyCRT_sig     = snd x' }

inline_for_extraction noextract
let synth_aliasKeyCRT_payload_t'
  (tbs_len: asn1_int32)
  (x: aliasKeyCRT_payload_t tbs_len)
: Tot (x': aliasKeyCRT_payload_t' tbs_len { x == synth_aliasKeyCRT_payload_t tbs_len x' })
= (x.aliasKeyCRT_tbs,
   x.aliasKeyCRT_sig_alg),
   x.aliasKeyCRT_sig

let parse_aliasKeyCRT_payload tbs_len
= parse_flbytes32 tbs_len
  `nondep_then`
  parse_algorithmIdentifier
  `nondep_then`
  parse_x509_signature
  `parse_synth`
  synth_aliasKeyCRT_payload_t tbs_len

let serialize_aliasKeyCRT_payload tbs_len
= serialize_synth
  (* p1 *) (parse_flbytes32 tbs_len
            `nondep_then`
            parse_algorithmIdentifier
            `nondep_then`
            parse_x509_signature)
  (* f2 *) (synth_aliasKeyCRT_payload_t tbs_len)
  (* s1 *) (serialize_flbytes32 tbs_len
            `serialize_nondep_then`
            serialize_algorithmIdentifier
            `serialize_nondep_then`
            serialize_x509_signature)
  (* g1 *) (synth_aliasKeyCRT_payload_t' tbs_len)
  (* prf*) ()

let lemma_serialize_aliasKeyCRT_payload_unfold tbs_len x
= serialize_nondep_then_eq
  (* s1 *) (serialize_flbytes32 tbs_len)
  (* s2 *) (serialize_algorithmIdentifier)
  (* in *) (fst (synth_aliasKeyCRT_payload_t' tbs_len x));
  serialize_nondep_then_eq
  (* s1 *) (serialize_flbytes32 tbs_len
            `serialize_nondep_then`
            serialize_algorithmIdentifier)
  (* s2 *) (serialize_x509_signature)
  (* in *) (synth_aliasKeyCRT_payload_t' tbs_len x);
  serialize_synth_eq
  (* p1 *) (parse_flbytes32 tbs_len
            `nondep_then`
            parse_algorithmIdentifier
            `nondep_then`
            parse_x509_signature)
  (* f2 *) (synth_aliasKeyCRT_payload_t tbs_len)
  (* s1 *) (serialize_flbytes32 tbs_len
            `serialize_nondep_then`
            serialize_algorithmIdentifier
            `serialize_nondep_then`
            serialize_x509_signature)
  (* g1 *) (synth_aliasKeyCRT_payload_t' tbs_len)
  (* prf*) ()
  (* in *) x

let lemma_serialize_aliasKeyCRT_payload_size tbs_len x
= lemma_serialize_aliasKeyCRT_payload_unfold tbs_len x;
  (**) lemma_serialize_algorithmIdentifier_size_exact x.aliasKeyCRT_sig_alg;
  (**) lemma_serialize_x509_signature_size      x.aliasKeyCRT_sig

let lemma_serialize_aliasKeyCRT_unfold tbs_len x
= lemma_serialize_asn1_sequence_TLV_unfold (serialize_aliasKeyCRT_payload tbs_len) x

let lemma_serialize_aliasKeyCRT_size tbs_len x
= lemma_serialize_asn1_sequence_TLV_size (serialize_aliasKeyCRT_payload tbs_len) x

let lemma_serialize_aliasKeyCRT_size_exact tbs_len x
= lemma_serialize_aliasKeyCRT_size tbs_len x;
  (**) lemma_serialize_aliasKeyCRT_payload_size tbs_len x


(* low *)

let serialize32_aliasKeyCRT_payload_backwards tbs_len
= serialize32_synth_backwards
  (* s1 *) (serialize32_flbytes32_backwards tbs_len
            `serialize32_nondep_then_backwards`
            serialize32_algorithmIdentifier_backwards
            `serialize32_nondep_then_backwards`
            serialize32_x509_signature_backwards)
  (* f2 *) (synth_aliasKeyCRT_payload_t  tbs_len)
  (* g1 *) (synth_aliasKeyCRT_payload_t' tbs_len)
  (* g1'*) (synth_aliasKeyCRT_payload_t' tbs_len)
  (* prf*) ()

let serialize32_aliasKeyCRT_backwards tbs_len
= coerce_serializer32_backwards
    (serialize_aliasKeyCRT tbs_len)
    (serialize32_asn1_sequence_TLV_backwards
       (serialize32_aliasKeyCRT_payload_backwards tbs_len))
    ()

