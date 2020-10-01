module X509.Crypto.Signature

open ASN1.Base
open ASN1.Spec
open ASN1.Low
open X509.Base
open FStar.Integers
module B32 = FStar.Bytes

let x509_signature_t_aux
= datatype_of_asn1_type BIT_STRING

let filter_x509_signature
  (x: x509_signature_t_aux)
: GTot (bool)
= let x = x <: datatype_of_asn1_type BIT_STRING in
  x.bs_len = 65ul &&
  x.bs_unused_bits = 0ul

let x509_signature_t
= parse_filter_refine filter_x509_signature

let parse_x509_signature_kind
= parse_asn1_TLV_kind_of_type BIT_STRING

val parse_x509_signature
: parser (parse_x509_signature_kind) (x509_signature_t)

val serialize_x509_signature
: serializer (parse_x509_signature)

val lemma_serialize_x509_signature_unfold
  (x: x509_signature_t)
: Lemma (
  serialize_x509_signature `serialize` x ==
  serialize_asn1_TLV_of_type BIT_STRING x
)

let length_of_x509_signature ()
: GTot (nat)
= 67

let len_of_x509_signature ()
: Tot (len: asn1_value_int32_of_type SEQUENCE
            { v len == length_of_x509_signature () })
= 67ul

val lemma_serialize_x509_signature_size
  (x: x509_signature_t)
: Lemma (
  length_of_opaque_serialization (serialize_x509_signature) x ==
  length_of_asn1_primitive_TLV #BIT_STRING x /\
  length_of_opaque_serialization (serialize_x509_signature) x ==
  length_of_x509_signature ()
)

(* Low *)
inline_for_extraction noextract
val serialize32_x509_signature_backwards
: serializer32_backwards (serialize_x509_signature)

(* Helpers *)

let x509_signature_raw_t
= B32.lbytes32 64ul

inline_for_extraction noextract
let x509_get_signature
  (sig32: x509_signature_raw_t)
: Tot (x509_signature_t)
= let sig_bs: x509_signature_t = Mkbit_string_t 65ul 0ul sig32 in
  (* Prf *) lemma_serialize_x509_signature_size sig_bs;
(* return *) sig_bs
