module ASN1.Low.Value.OID

open ASN1.Base
open ASN1.Spec.Value.OID
open ASN1.Low.Base
open LowParse.Low.Bytes

open FStar.Integers

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module MB = LowStar.Monotonic.Buffer
module B = LowStar.Buffer
module Cast = FStar.Int.Cast

module B32 = FStar.Bytes

module IB = LowStar.ImmutableBuffer
module CB = LowStar.ConstBuffer

module G = FStar.Ghost

friend ASN1.Spec.Value.OID

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
let len_of_oid
  (oid: oid_t)
: Tot (len: asn1_value_int32_of_type OID
      { v len == length_of_oid oid })
= match oid with
  | OID_RIOT                     -> 9ul
  | OID_AT_CN                    -> 3ul
  | OID_AT_COUNTRY               -> 3ul
  | OID_AT_ORGANIZATION          -> 3ul
  | OID_CLIENT_AUTH              -> 7ul
  | OID_AUTHORITY_KEY_IDENTIFIER -> 3ul
  | OID_KEY_USAGE                -> 3ul
  | OID_EXTENDED_KEY_USAGE       -> 3ul
  | OID_BASIC_CONSTRAINTS        -> 3ul
  | OID_DIGEST_SHA256            -> 9ul
  | OID_EC_ALG_UNRESTRICTED      -> 5ul
  | OID_EC_GRP_SECP256R1         -> 6ul
  | OID_ED25519                  -> 3ul
  | OID_X25519                   -> 3ul
  | OID_PKCS9_CSR_EXT_REQ        -> 9ul

(* FIXME: The order will affect Z3 for some reason. *)
let oid_buffer_of_oid
  (oid: oid_t)
= match oid with
  | OID_RIOT                     -> oid_RIOT_as_buffer
  | OID_AT_CN                    -> oid_AT_CN_as_buffer
  | OID_AT_COUNTRY               -> oid_AT_COUNTRY_as_buffer
  | OID_AT_ORGANIZATION          -> oid_AT_ORGANIZATION_as_buffer
  | OID_CLIENT_AUTH              -> oid_CLIENT_AUTH_as_buffer
  | OID_AUTHORITY_KEY_IDENTIFIER -> oid_AUTHORITY_KEY_IDENTIFIER_as_buffer
  | OID_KEY_USAGE                -> oid_KEY_USAGE_as_buffer
  | OID_EXTENDED_KEY_USAGE       -> oid_EXTENDED_KEY_USAGE_as_buffer
  | OID_BASIC_CONSTRAINTS        -> oid_BASIC_CONSTRAINTS_as_buffer
  | OID_EC_ALG_UNRESTRICTED      -> oid_EC_ALG_UNRESTRICTED_as_buffer
  | OID_EC_GRP_SECP256R1         -> oid_EC_GRP_SECP256R1_as_buffer
  | OID_ED25519                  -> oid_ED25519_as_bufffer
  | OID_X25519                   -> oid_X25519_as_bufffer
  | OID_DIGEST_SHA256            -> oid_DIGEST_ALG_SHA256_as_buffer
  | OID_PKCS9_CSR_EXT_REQ        -> oid_PKCS9_CSR_EXT_REQ_as_buffer

let len_of_oid_buffer
  (oid: oid_t)
: Tot (len: asn1_value_int32_of_type OID
      { v len == B.length (oid_buffer_of_oid oid) /\
        v len == length_of_oid oid })
= match oid with
  | OID_RIOT                     -> 9ul //oid_RIOT_as_buffer
  | OID_AT_CN                    -> 3ul //oid_AT_CN_as_buffer
  | OID_AT_COUNTRY               -> 3ul //oid_AT_COUNTRY_as_buffer
  | OID_AT_ORGANIZATION          -> 3ul //oid_AT_ORGANIZATION_as_buffer
  | OID_CLIENT_AUTH              -> 7ul //oid_CLIENT_AUTH_as_buffer
  | OID_AUTHORITY_KEY_IDENTIFIER -> 3ul //oid_AUTHORITY_KEY_IDENTIFIER_as_buffer
  | OID_KEY_USAGE                -> 3ul //oid_KEY_USAGE_as_buffer
  | OID_EXTENDED_KEY_USAGE       -> 3ul //oid_EXTENDED_KEY_USAGE_as_buffer
  | OID_BASIC_CONSTRAINTS        -> 3ul //oid_BASIC_CONSTRAINTS_as_buffer
  | OID_EC_ALG_UNRESTRICTED      -> 5ul //oid_EC_ALG_UNRESTRICTED_as_buffer
  | OID_EC_GRP_SECP256R1         -> 6ul //oid_EC_GRP_SECP256R1_as_buffer
  | OID_ED25519                  -> 3ul
  | OID_X25519                   -> 3ul
  | OID_DIGEST_SHA256            -> 9ul //oid_DIGEST_ALG_SHA256_as_buffer
  | OID_PKCS9_CSR_EXT_REQ        -> 9ul

noextract
let seq_of_oid_buffer
  (oid: oid_t)
: Tot (s: bytes {List.mem s known_oids_as_seq /\
                 B.witnessed (oid_buffer_of_oid oid) (IB.cpred s) /\
                 Seq.length s == length_of_oid oid})
= lemma_known_oids_as_seq_contains_oid_seq_of oid;
  oid_seq_of oid

#restart-solver
#push-options "--z3rlimit 64 --fuel 0 --ifuel 0"
inline_for_extraction
let serialize32_asn1_oid_backwards
  (len: asn1_value_int32_of_type OID)
: Tot (serializer32_backwards (serialize_asn1_oid (v len)))
= fun (oid: oid_t { Seq.length (oid_seq_of oid) == v len })
    (#rrel #rel: _)
    (b: B.mbuffer byte rrel rel)
    (pos: size_t)
-> (* Prf *) lemma_serialize_asn1_oid_unfold (v len) oid;
   (* Prf *) lemma_serialize_asn1_oid_size (v len) oid;
   let oid_buffer = oid_buffer_of_oid oid in
   (* Prf *) B.recall oid_buffer;
   (* Prf *) IB.recall_contents oid_buffer (seq_of_oid_buffer oid);

   let offset = len_of_oid_buffer oid in

   store_bytes
     (* s32 *) (B32.of_buffer offset oid_buffer)
     (*range*) 0ul offset
     (* dst *) b
     (* pos *) (pos - offset);

(* return *) offset
#pop-options

open ASN1.Spec.Tag
open ASN1.Spec.Length
open ASN1.Low.Tag
open ASN1.Low.Length

inline_for_extraction
let parser_tag_of_oid_impl
  (x: datatype_of_asn1_type OID)
: Tot (tg: (the_asn1_tag OID & asn1_value_int32_of_type OID)
      { tg == parser_tag_of_oid x })
= (OID, len_of_oid_buffer x)

inline_for_extraction
let synth_asn1_oid_V_inverse_impl
  (tg: (the_asn1_tag OID & asn1_value_int32_of_type OID))
  (value': refine_with_tag parser_tag_of_oid tg)
: Tot (value: datatype_of_asn1_type OID
      { length_of_oid value == v (snd tg) /\
        value == synth_asn1_oid_V_inverse tg value' })
= value'

#push-options "--z3rlimit 32 --fuel 0 --ifuel 0"
let serialize32_asn1_oid_TLV_backwards ()
: Tot (serializer32_backwards serialize_asn1_oid_TLV)
= serialize32_tagged_union_backwards
  (* lst *) (serialize32_asn1_tag_of_type_backwards OID
             `serialize32_nondep_then_backwards`
             serialize32_asn1_length_of_type_backwards OID)
  (* tg  *) (parser_tag_of_oid_impl)
  (* ls  *) (fun x -> (serialize32_synth_backwards
                     (* ls1 *) (weak_kind_of_type OID
                                `serialize32_weaken_backwards`
                                serialize32_asn1_oid_backwards (snd x))
                     (* f2  *) (synth_asn1_oid_V x)
                     (* g1  *) (synth_asn1_oid_V_inverse x)
                     (* g1' *) (synth_asn1_oid_V_inverse_impl x)
                     (* Prf *) ()))
#pop-options

noextract inline_for_extraction
let serialize32_asn1_oid_TLV_of_backwards
  (oid: datatype_of_asn1_type OID)
: serializer32_backwards (serialize_asn1_oid_TLV_of oid)
= //serialize32_synth_backwards
  (* s1 *) (serialize32_asn1_oid_TLV_backwards ()
            `serialize32_filter_backwards`
            filter_asn1_oid_TLV_of oid)
  // (* f2 *) (fun x -> x <: x: datatype_of_asn1_type OID {x == oid})
  // (* g1 *) (fun x -> x <: parse_filter_refine (filter_asn1_oid_TLV_of oid))
  // (* g1'*) (fun x -> x <: parse_filter_refine (filter_asn1_oid_TLV_of oid))
  // (* prf*) ()

inline_for_extraction
let serialize32_envelop_OID_with_backwards
  (oid: datatype_of_asn1_type OID)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (#s: serializer p)
  (s32: serializer32_backwards s)
: serializer32_backwards (serialize_envelop_OID_with oid s)
= serialize32_asn1_oid_TLV_of_backwards oid
  `serialize32_nondep_then_backwards`
  s32
