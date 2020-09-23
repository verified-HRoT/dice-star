module ASN1.Low.Value.OID

open ASN1.Base
open ASN1.Spec.Value.OID
open ASN1.Low.Base

open FStar.Integers

module HS = FStar.HyperStack

module B = LowStar.Buffer
module IB = LowStar.ImmutableBuffer

(* FIXME: Notes about `IB` and Ghost seq:
   NOTE: `IB.cpred` vs `IB.seq_eq`, `IB.recall_contents` vs `IB.recall_value`
   We may want to use the following `oid_seq` to represent a
   immutable buffer, but now the `IB` library is not universally
   using ghost seq, becau se HACL* is dependent on the legacy `IB`
   which is using (witnessing, recalling over) (total) seq. The
   allocation function `IB.igcmalloc_of_list` is one of those
   blocked by HACL*.
*)

// noeq
// type oid_buffer_t = {
//   oid_len: asn1_value_int32_of_type OID;
//   oid_seq: G.erased (lbytes (v oid_len));
//   oid_buf: ib: IB.libuffer byte (v oid_len) (G.reveal oid_seq) {
//            B.frameOf ib == HS.root /\
//            B.recallable ib
//   }
// }

(* ZT: Noramlize them here instead of mark OID lists as unfold and normalize them everywhere. *)
let oid_RIOT_as_buffer                     = IB.igcmalloc_of_list HS.root (oid_RIOT)
let oid_AT_CN_as_buffer                    = IB.igcmalloc_of_list HS.root (oid_AT_CN)
let oid_AT_COUNTRY_as_buffer               = IB.igcmalloc_of_list HS.root (oid_AT_COUNTRY)
let oid_AT_ORGANIZATION_as_buffer          = IB.igcmalloc_of_list HS.root (oid_AT_ORGANIZATION)
let oid_CLIENT_AUTH_as_buffer              = IB.igcmalloc_of_list HS.root (oid_CLIENT_AUTH)
let oid_AUTHORITY_KEY_IDENTIFIER_as_buffer = IB.igcmalloc_of_list HS.root (oid_AUTHORITY_KEY_IDENTIFIER)
let oid_KEY_USAGE_as_buffer                = IB.igcmalloc_of_list HS.root (oid_KEY_USAGE)
let oid_EXTENDED_KEY_USAGE_as_buffer       = IB.igcmalloc_of_list HS.root (oid_EXTENDED_KEY_USAGE)
let oid_BASIC_CONSTRAINTS_as_buffer        = IB.igcmalloc_of_list HS.root (oid_BASIC_CONSTRAINTS)
let oid_EC_ALG_UNRESTRICTED_as_buffer      = IB.igcmalloc_of_list HS.root (oid_EC_ALG_UNRESTRICTED)
let oid_EC_GRP_SECP256R1_as_buffer         = IB.igcmalloc_of_list HS.root (oid_EC_GRP_SECP256R1)
let oid_DIGEST_ALG_SHA256_as_buffer        = IB.igcmalloc_of_list HS.root (oid_DIGEST_ALG_SHA256)
let oid_ED25519_as_bufffer                 = IB.igcmalloc_of_list HS.root (oid_ED25519)
let oid_X25519_as_bufffer                  = IB.igcmalloc_of_list HS.root (oid_X25519)
let oid_PKCS9_CSR_EXT_REQ_as_buffer        = IB.igcmalloc_of_list HS.root (oid_PKCS9_CSR_EXT_REQ)



(* FIXME: A workaround
   To not extract any (total) seq, we split the `oid_buffer_t` into three
   functions, all of them take an `oid: oid_t`, returns the corresponding
   len, (total) seq and ibuffer. The (total) seq will be only used in the
   `IB.recall_contents` lemma, and the function returns the (total) seq
   will be marded as `noextract`.
*)

noextract
val len_of_oid
  (oid: oid_t)
: Tot (len: asn1_value_int32_of_type OID
      { v len == length_of_oid oid })

(* FIXME: The order will affect Z3 for some reason. *)
val oid_buffer_of_oid
  (oid: oid_t) : IB.ibuffer UInt8.t

val len_of_oid_buffer
  (oid: oid_t)
: Tot (len: asn1_value_int32_of_type OID
      { v len == B.length (oid_buffer_of_oid oid) /\
        v len == length_of_oid oid })

inline_for_extraction
val serialize32_asn1_oid_backwards
  (len: asn1_value_int32_of_type OID)
: (serializer32_backwards (serialize_asn1_oid (v len)))


val serialize32_asn1_oid_TLV_backwards (_:unit)
: (serializer32_backwards serialize_asn1_oid_TLV)

noextract inline_for_extraction
val serialize32_asn1_oid_TLV_of_backwards
  (oid: datatype_of_asn1_type OID)
: serializer32_backwards (serialize_asn1_oid_TLV_of oid)

inline_for_extraction
val serialize32_envelop_OID_with_backwards
  (oid: datatype_of_asn1_type OID)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (#s: serializer p)
  (s32: serializer32_backwards s)
: serializer32_backwards (serialize_envelop_OID_with oid s)
