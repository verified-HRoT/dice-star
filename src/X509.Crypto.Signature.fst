module X509.Crypto.Signature

open LowParse.Low.Base
// open LowParse.Low.Combinators

open ASN1.Spec
open ASN1.Low

open X509.Base

open FStar.Integers
module B32 = FStar.Bytes

open ASN1.Base

let x509_signature_t_aux
  (alg: supported_crypto_alg_t {alg == AlgID_Ed25519})
= match alg with
  | AlgID_Ed25519   -> datatype_of_asn1_type BIT_STRING

let filter_x509_signature
  (alg: supported_crypto_alg_t {alg == AlgID_Ed25519})
  (x: x509_signature_t_aux alg)
: GTot (bool)
= match alg with
  | AlgID_Ed25519   -> ( let x = x <: datatype_of_asn1_type BIT_STRING in
                   x.bs_len = 65ul &&
                   x.bs_unused_bits = 0ul )

let x509_signature_t
  (alg: supported_crypto_alg_t {alg == AlgID_Ed25519})
= match alg with
  | AlgID_Ed25519   -> ( bs: datatype_of_asn1_type BIT_STRING
                       { v bs.bs_len == 65 /\
                         v bs.bs_unused_bits == 0 })

let parse_x509_signature_kind
  (alg: supported_crypto_alg_t {alg == AlgID_Ed25519})
= match alg with
  | AlgID_Ed25519   -> parse_asn1_TLV_kind_of_type BIT_STRING

let parse_x509_signature
  (alg: supported_crypto_alg_t {alg == AlgID_Ed25519})
: parser (parse_x509_signature_kind alg) (x509_signature_t alg)
= match alg with
  | AlgID_Ed25519   -> ( parse_asn1_TLV_of_type BIT_STRING
                   `parse_filter`
                   filter_x509_signature alg
                   `parse_synth`
                   (fun x -> x <: x509_signature_t alg))

let serialize_x509_signature
  (alg: supported_crypto_alg_t {alg == AlgID_Ed25519})
: serializer (parse_x509_signature alg)
= match alg with
  | AlgID_Ed25519   -> ( serialize_synth
                   (* p1 *) (parse_asn1_TLV_of_type BIT_STRING
                             `parse_filter`
                             filter_x509_signature alg)
                   (* f2 *) (fun x -> x <: x509_signature_t alg)
                   (* s1 *) (serialize_asn1_TLV_of_type BIT_STRING
                             `serialize_filter`
                             filter_x509_signature alg)
                   (* g1 *) (fun x -> x <: parse_filter_refine (filter_x509_signature alg))
                   (* prf*) () )

let lemma_serialize_x509_signature_unfold
  (alg: supported_crypto_alg_t {alg == AlgID_Ed25519})
  (x: x509_signature_t alg)
: Lemma (
  match alg with
  | AlgID_Ed25519   -> ( serialize_x509_signature alg `serialize` x ==
                   serialize_asn1_TLV_of_type BIT_STRING x )
)
= serialize_synth_eq
  (* p1 *) (parse_asn1_TLV_of_type BIT_STRING
            `parse_filter`
            filter_x509_signature alg)
  (* f2 *) (fun x -> x <: x509_signature_t alg)
  (* s1 *) (serialize_asn1_TLV_of_type BIT_STRING
            `serialize_filter`
            filter_x509_signature alg)
  (* g1 *) (fun x -> x <: parse_filter_refine (filter_x509_signature alg))
  (* prf*) ()
  (* in *) x

let lemma_serialize_x509_signature_size
  (alg: supported_crypto_alg_t {alg == AlgID_Ed25519})
  (x: x509_signature_t alg)
: Lemma (
  match alg with
  | AlgID_Ed25519   -> ( length_of_opaque_serialization (serialize_x509_signature alg) x ==
                   length_of_asn1_primitive_TLV #BIT_STRING x /\
                   length_of_opaque_serialization (serialize_x509_signature alg) x == 67 )
)
= match alg with
  | AlgID_Ed25519   -> ( lemma_serialize_x509_signature_unfold alg x;
                   lemma_serialize_asn1_bit_string_TLV_size x )

let x509_signature_t_inbound
  (alg: supported_crypto_alg_t {alg == AlgID_Ed25519})
= match alg with
  | AlgID_Ed25519   -> ( inbound_sequence_value_of (serialize_x509_signature alg) )

let parse_x509_signature_sequence_TLV
  (alg: supported_crypto_alg_t {alg == AlgID_Ed25519})
: parser _ (x509_signature_t_inbound alg)
= match alg with
  | AlgID_Ed25519   -> ( parse_asn1_sequence_TLV (serialize_x509_signature alg) )

let serialize_x509_signature_sequence_TLV
  (alg: supported_crypto_alg_t {alg == AlgID_Ed25519})
: serializer (parse_x509_signature_sequence_TLV alg)
= match alg with
  | AlgID_Ed25519   -> ( serialize_asn1_sequence_TLV (serialize_x509_signature alg) )

let lemma_serialize_x509_signature_sequence_TLV_unfold
  (alg: supported_crypto_alg_t {alg == AlgID_Ed25519})
  (x: x509_signature_t_inbound alg)
: Lemma ( predicate_serialize_asn1_sequence_TLV_unfold (serialize_x509_signature alg) x )
= match alg with
  | AlgID_Ed25519   -> ( lemma_serialize_asn1_sequence_TLV_unfold (serialize_x509_signature alg) x )

let lemma_serialize_x509_signature_sequence_TLV_size
  (alg: supported_crypto_alg_t {alg == AlgID_Ed25519})
  (x: x509_signature_t_inbound alg)
: Lemma ( predicate_serialize_asn1_sequence_TLV_size (serialize_x509_signature alg) x )
= match alg with
  | AlgID_Ed25519   -> ( lemma_serialize_asn1_sequence_TLV_size (serialize_x509_signature alg) x )

#push-options "--z3rlimit 32 --fuel 4 --ifuel 4"
let lemma_serialize_x509_signature_sequence_TLV_size_exact
  (alg: supported_crypto_alg_t {alg == AlgID_Ed25519})
  (x: x509_signature_t_inbound alg)
: Lemma (
  match alg with
  | AlgID_Ed25519    -> ( length_of_opaque_serialization (serialize_x509_signature_sequence_TLV alg) x == 69 )
)
= match alg with
  | AlgID_Ed25519    -> ( lemma_serialize_x509_signature_sequence_TLV_size alg x;
                    lemma_serialize_x509_signature_size alg x )
#pop-options

(* Low *)
inline_for_extraction
let serialize32_x509_signature_backwards
  (alg: supported_crypto_alg_t {alg == AlgID_Ed25519})
: serializer32_backwards (serialize_x509_signature alg)
= match alg with
  | AlgID_Ed25519   -> ( serialize32_synth_backwards
                   (* s32 *) (serialize32_asn1_bit_string_TLV_backwards ()
                              `serialize32_filter_backwards`
                              filter_x509_signature alg)
                   (* f2  *) (fun x -> x <: x509_signature_t alg)
                   (* g1  *) (fun x -> x <: parse_filter_refine (filter_x509_signature alg))
                   (* g1' *) (fun x -> x <: parse_filter_refine (filter_x509_signature alg))
                   (* prf *) () )

inline_for_extraction
let serialize32_x509_signature_sequence_TLV_backwards
  (alg: supported_crypto_alg_t {alg == AlgID_Ed25519})
: serializer32_backwards (serialize_x509_signature_sequence_TLV alg)
= match alg with
  | AlgID_Ed25519   -> ( serialize32_asn1_sequence_TLV_backwards (serialize32_x509_signature_backwards alg) )


(* Helpers *)
let _ = assert (length_of_oid OID_EC_GRP_SECP256R1 == 6)

module B32 = FStar.Bytes
let x509_signature_raw_t
  (alg: supported_crypto_alg_t {alg == AlgID_Ed25519})
= match alg with
  | AlgID_Ed25519   -> ( B32.lbytes32 64ul )

let x509_get_signature
  (alg: supported_crypto_alg_t {alg == AlgID_Ed25519})
  (sig32: x509_signature_raw_t alg)
: Tot (x509_signature_t_inbound alg)
=
  match alg with
  | AlgID_Ed25519   -> ( let sig_bs: x509_signature_t alg = Mkbit_string_t 65ul 0ul sig32 in
                   (* Prf *) lemma_serialize_x509_signature_size alg sig_bs;
                   (* return *) sig_bs )
