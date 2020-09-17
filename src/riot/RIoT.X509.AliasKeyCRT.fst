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

#push-options "--z3rlimit 32"
type aliasKeyCRT_payload_t (tbs_len: asn1_int32) = {
  aliasKeyCRT_tbs: B32.lbytes32 tbs_len;
  aliasKeyCRT_sig_alg: algorithmIdentifier_t;
  aliasKeyCRT_sig: x509_signature_t
}
#pop-options

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

let synth_aliasKeyCRT_payload_t'
  (tbs_len: asn1_int32)
  (x: aliasKeyCRT_payload_t tbs_len)
: Tot (x': aliasKeyCRT_payload_t' tbs_len { x == synth_aliasKeyCRT_payload_t tbs_len x' })
= (x.aliasKeyCRT_tbs,
   x.aliasKeyCRT_sig_alg),
   x.aliasKeyCRT_sig

let parse_aliasKeyCRT_payload
  (tbs_len: asn1_int32)
: parser _ (aliasKeyCRT_payload_t tbs_len)
= parse_flbytes32 tbs_len
  `nondep_then`
  parse_algorithmIdentifier
  `nondep_then`
  parse_x509_signature
  `parse_synth`
  synth_aliasKeyCRT_payload_t tbs_len

let serialize_aliasKeyCRT_payload
  (tbs_len: asn1_int32)
: serializer (parse_aliasKeyCRT_payload tbs_len)
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

let lemma_serialize_aliasKeyCRT_payload_unfold
  (tbs_len: asn1_int32)
  (x: aliasKeyCRT_payload_t tbs_len)
: Lemma (
  serialize_aliasKeyCRT_payload tbs_len `serialize` x ==
 (serialize_flbytes32 tbs_len `serialize` x.aliasKeyCRT_tbs)
  `Seq.append`
 (serialize_algorithmIdentifier `serialize` x.aliasKeyCRT_sig_alg)
  `Seq.append`
 (serialize_x509_signature `serialize` x.aliasKeyCRT_sig)
)
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

let length_of_aliasKeyCRT_payload
  (tbs_len: asn1_int32)
: GTot (nat)
= v tbs_len + 74

#push-options "--z3rlimit 32"
let len_of_aliasKeyCRT_payload
  (tbs_len: asn1_int32
            { length_of_aliasKeyCRT_payload tbs_len
              <= asn1_value_length_max_of_type SEQUENCE })
: Tot (len: asn1_TLV_int32_of_type SEQUENCE
            { v len == length_of_aliasKeyCRT_payload tbs_len })
= tbs_len + 74ul
#pop-options

#restart-solver
#push-options "--z3rlimit 64 --fuel 0 --ifuel 0"
let lemma_serialize_aliasKeyCRT_payload_size
  (tbs_len: asn1_int32)
  (x: aliasKeyCRT_payload_t tbs_len)
: Lemma (
  (* unfold *)
  length_of_opaque_serialization (serialize_aliasKeyCRT_payload tbs_len) x ==
  length_of_opaque_serialization (serialize_flbytes32 tbs_len) x.aliasKeyCRT_tbs +
  length_of_opaque_serialization (serialize_algorithmIdentifier) x.aliasKeyCRT_sig_alg +
  length_of_opaque_serialization (serialize_x509_signature) x.aliasKeyCRT_sig /\
  (* exact size *)
  length_of_opaque_serialization (serialize_aliasKeyCRT_payload tbs_len) x
  == length_of_aliasKeyCRT_payload tbs_len
)
= lemma_serialize_aliasKeyCRT_payload_unfold tbs_len x;
  (**) lemma_serialize_algorithmIdentifier_size_exact x.aliasKeyCRT_sig_alg;
  (**) lemma_serialize_x509_signature_size      x.aliasKeyCRT_sig
#pop-options


(* SEQUENCE TLV*)
let aliasKeyCRT_t
  (tbs_len: asn1_int32)
= inbound_sequence_value_of (serialize_aliasKeyCRT_payload tbs_len)

let parse_aliasKeyCRT
  (tbs_len: asn1_int32)
: parser (parse_asn1_envelop_tag_with_TLV_kind SEQUENCE) (aliasKeyCRT_t tbs_len)
= aliasKeyCRT_t tbs_len
  `coerce_parser`
  parse_asn1_sequence_TLV (serialize_aliasKeyCRT_payload tbs_len)

let serialize_aliasKeyCRT
  (tbs_len: asn1_int32)
: serializer (parse_aliasKeyCRT tbs_len)
= coerce_parser_serializer
    (parse_aliasKeyCRT tbs_len)
    (serialize_asn1_sequence_TLV (serialize_aliasKeyCRT_payload tbs_len))
    ()

let lemma_serialize_aliasKeyCRT_unfold
  (tbs_len: asn1_int32)
  (x: aliasKeyCRT_t tbs_len)
: Lemma ( predicate_serialize_asn1_sequence_TLV_unfold (serialize_aliasKeyCRT_payload tbs_len) x )
= lemma_serialize_asn1_sequence_TLV_unfold (serialize_aliasKeyCRT_payload tbs_len) x

let lemma_serialize_aliasKeyCRT_size
  (tbs_len: asn1_int32)
  (x: aliasKeyCRT_t tbs_len)
: Lemma ( predicate_serialize_asn1_sequence_TLV_size (serialize_aliasKeyCRT_payload tbs_len) x )
= lemma_serialize_asn1_sequence_TLV_size (serialize_aliasKeyCRT_payload tbs_len) x

#push-options "--z3rlimit 64 --fuel 0 --ifuel 0"
let length_of_aliasKeyCRT
  (tbs_len: asn1_int32
            { length_of_aliasKeyCRT_payload tbs_len
              <= asn1_value_length_max_of_type SEQUENCE })
: GTot (asn1_TLV_length_of_type SEQUENCE)
= length_of_TLV
    (SEQUENCE)
    ((length_of_aliasKeyCRT_payload tbs_len))

let len_of_aliasKeyCRT
  (tbs_len: asn1_int32
            { length_of_aliasKeyCRT_payload tbs_len
              <= asn1_value_length_max_of_type SEQUENCE })
: Tot (len: asn1_TLV_int32_of_type SEQUENCE
            { v len == length_of_aliasKeyCRT tbs_len })
= len_of_TLV
    (SEQUENCE)
    (len_of_aliasKeyCRT_payload tbs_len)
#pop-options

#push-options "--z3rlimit 64 --fuel 0 --ifuel 0"
let lemma_serialize_aliasKeyCRT_size_exact
  (tbs_len: asn1_int32)
  (x: aliasKeyCRT_t tbs_len)
: Lemma (
  let _ = lemma_serialize_aliasKeyCRT_payload_size tbs_len x in
  (* exact size *)
  length_of_opaque_serialization (serialize_aliasKeyCRT tbs_len) x
  == length_of_aliasKeyCRT tbs_len /\
  (* upper bound *)
  length_of_opaque_serialization (serialize_aliasKeyCRT tbs_len) x
  <= v tbs_len + 84
)
= lemma_serialize_aliasKeyCRT_size tbs_len x;
  (**) lemma_serialize_aliasKeyCRT_payload_size tbs_len x
#pop-options


(* low *)

let serialize32_aliasKeyCRT_payload_backwards
  (tbs_len: asn1_int32)
: serializer32_backwards (serialize_aliasKeyCRT_payload tbs_len)
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

let serialize32_aliasKeyCRT_backwards
  (tbs_len: asn1_int32)
: serializer32_backwards (serialize_aliasKeyCRT tbs_len)
= coerce_serializer32_backwards
    (serialize_aliasKeyCRT tbs_len)
    (serialize32_asn1_sequence_TLV_backwards
       (serialize32_aliasKeyCRT_payload_backwards tbs_len))
    ()

#restart-solver
#push-options "--z3rlimit 32 --fuel 0 --ifuel 0"
let x509_get_AliasKeyCRT
  (tbs_len: asn1_int32
            { length_of_aliasKeyCRT_payload tbs_len <= asn1_value_length_max_of_type SEQUENCE })
  (aliasKeyCRT_tbs: B32.lbytes32 tbs_len)
  (signature32: x509_signature_raw_t) // B32.lbytes32 64ul
: Tot (aliasKeyCRT_t tbs_len)
=
  let aliasKeyCRT_sig_alg = x509_get_algorithmIdentifier () in
  (* Prf *) lemma_serialize_algorithmIdentifier_size_exact aliasKeyCRT_sig_alg;

  let aliasKeyCRT_sig = x509_get_signature signature32 in
  (* Prf *) lemma_serialize_x509_signature_size aliasKeyCRT_sig;

  let aliasKeyCRT: aliasKeyCRT_payload_t tbs_len = {
    aliasKeyCRT_tbs     = aliasKeyCRT_tbs;
    aliasKeyCRT_sig_alg = aliasKeyCRT_sig_alg;
    aliasKeyCRT_sig     = aliasKeyCRT_sig
  } in
  (* Prf *) lemma_serialize_aliasKeyCRT_payload_unfold tbs_len aliasKeyCRT;
  (* Prf *) lemma_serialize_aliasKeyCRT_payload_size   tbs_len aliasKeyCRT;
  (* Prf *) (**) lemma_serialize_flbytes32_size tbs_len aliasKeyCRT.aliasKeyCRT_tbs;

(* return *) aliasKeyCRT
