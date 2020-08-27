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


// #push-options "--z3rlimit 32"
// inline_for_extraction
// let blit_from_ib
//   (len: size_t)
//   (src_seq: lbytes (v len))
//   (src: IB.libuffer byte (v len) src_seq {B.frameOf src == HS.root /\ B.recallable src})
//   (src_from src_to: size_t)
//   (#rrel #rel: _)
//   (dst: B.mbuffer byte rrel rel)
//   (dst_pos: size_t)
// : HST.Stack unit
//   (requires (fun h ->
//     B.live h dst /\
//     v src_from <= v src_to /\ v src_to <= B.length src /\
//     v dst_pos + (v src_to - v src_from) <= B.length dst /\
//     writable dst (v dst_pos) (v dst_pos + (v src_to - v src_from)) h
//   ))
//   (ensures (fun h _ h' ->
//     B.modifies (B.loc_buffer_from_to dst dst_pos (dst_pos + (src_to - src_from))) h h' /\
//     Seq.slice (B.as_seq h' dst) (v dst_pos) (v dst_pos + (v src_to - v src_from)) == Seq.slice (B.as_seq h src) (v src_from) (v src_to)
//   ))
// = let h0 = HST.get () in
//   HST.push_frame ();
//   let h1 = HST.get () in
//   let bi: B.pointer size_t = B.alloca 0ul 1ul in
//   let h2 = HST.get () in
//   let len = src_to - src_from in
//   C.Loops.do_while
//     (fun h stop ->
//       B.modifies (B.loc_union (B.loc_region_only true (HS.get_tip h1)) (B.loc_buffer_from_to dst dst_pos (dst_pos + len))) h2 h /\
//       B.live h bi /\ (
//       let i = Seq.index (B.as_seq h bi) 0 in
//       v i <= v len /\
//       writable dst (v dst_pos) (v dst_pos + v len) h /\
//       Seq.slice (B.as_seq h dst) (v dst_pos) (v dst_pos + v i) `Seq.equal` Seq.slice (B.as_seq h src) (v src_from) (v src_from + v i) /\
//       (stop == true ==> i == len)
//     ))
//     (fun _ ->
//       let i = B.index bi 0ul in
//       if i = len
//       then true
//       else begin
//         (**) let h = HST.get () in
//         (**) assume (Seq.slice (B.as_seq h dst) (v dst_pos) (v dst_pos + v (B.as_seq h bi).[0])
//                      `Seq.equal`
//                      Seq.slice (B.as_seq h src) (v src_from) (v src_from + v (B.as_seq h bi).[0]));
//         (**) B.recall src;
//         (**) IB.recall_contents src src_seq;
//         (**) let h = HST.get () in
//         let x = B.index src (src_from + i) in
//         mbuffer_upd dst (Ghost.hide (v dst_pos)) (Ghost.hide (v dst_pos + v len)) (dst_pos + i) x;

//         let i': size_t = i + 1ul in
//         B.upd bi 0ul i';

//         (**) let h' = HST.get () in
//         (**) IB.recall_contents src src_seq;
//         (**) Seq.lemma_split (Seq.slice (B.as_seq h' dst) (v dst_pos) (v dst_pos + v i')) (v i);
//         (**) assert ((B.as_seq h' dst).[v (dst_pos + i)] == (B.as_seq h' src).[v (src_from + i)]);
//         (**) let h = HST.get () in
//         (**) assert (Seq.slice (B.as_seq h dst) (v dst_pos) (v dst_pos + v (B.as_seq h bi).[0])
//                      `Seq.equal`
//                      Seq.slice (B.as_seq h src) (v src_from) (v src_from + v (B.as_seq h bi).[0]));
//         admit ();
//         i' = len
//       end
//     )
//     ;
//   HST.pop_frame ()
// #pop-options


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

  (*WIP: modifies proof is the last piece.*)
   // (* Prf *) let h0 = HST.get () in
   // C.Loops.for
   //   (* start*) 0ul
   //   (* end  *) offset
   //   (* inv  *) (fun (h: HS.mem) (i: nat) ->
   //                 let s_src = B.as_seq h oid_buffer in
   //                 let s_dst = B.as_seq h b in
   //                 //0 < i /\ i < v offset /\ //within_bounds (Unsigned W32) i /\
   //                 // B.live h b /\ B.modifies (B.loc_buffer_from_to b (pos - offset) (pos - offset + u i)) h0 h /\
   //                 writable b (v pos - v offset) (v pos) h /\
   //                 i <= Seq.length s_src /\s_src == seq_of_oid_buffer oid /\
   //                 Seq.slice s_src 0 i `Seq.equal` Seq.slice s_dst (v pos - v offset) (v pos - v offset + i)
   //                 )
   //   (* body *) (fun i32 ->
   //                 (* Prf *) let h1 = HST.get () in
   //                 (* Prf *) IB.recall oid_buffer;
   //                 (* Prf *) IB.recall_contents oid_buffer (seq_of_oid_buffer oid);
   //                 let x = B.index oid_buffer i32 in
   //                 mbuffer_upd
   //                   (* buf *) b
   //                   (*range*) (v pos - v offset) (v pos)
   //                   (* pos *) (pos - offset + i32)
   //                   (* val *) x;
   //                 (* Prf *) IB.recall_contents oid_buffer (seq_of_oid_buffer oid);
   //                 (* Prf *) let h2 = HST.get () in
   //                 (* Prf *) assert (writable b (v pos - v offset) (v pos) h2 /\ B.live h2 b);
   //                 (* Prf *) B.modifies_buffer_from_to_elim
   //                           (* buf *) b
   //                           (*frame*) (pos - offset) (pos - offset + i32)
   //                           (* new *) (B.loc_buffer_from_to b (pos - offset + i32) (pos - offset + i32 + 1ul))
   //                           (* mem *) h1 h2;
   //                 (* Prf *) Seq.lemma_split
   //                           (* s *) (Seq.slice (B.as_seq h2 b) (v pos - v offset) (v pos - v offset + v i32 + 1))
   //                           (*pos*) (v i32);
   //                 (* Prf *) Seq.lemma_split
   //                           (* s *) (Seq.slice (B.as_seq h2 oid_buffer) 0 (v i32 + 1))
   //                           (*pos*) (v i32);
   //                           assert (let s_src = B.as_seq h2 oid_buffer in
   //                                   let s_dst = B.as_seq h2 b in
   //                                   Seq.slice s_src 0 (v i32) `Seq.equal` Seq.slice s_dst (v pos - v offset) (v pos - v offset + v i32));
   //                 (* Prf *) assert (let s_src = B.as_seq h2 oid_buffer in
   //                                   let s_dst = B.as_seq h2 b in
   //                                   s_dst.[v pos - v offset + v i32] == s_src.[v i32] /\
   //                                   Seq.slice s_src 0 (v i32) `Seq.equal` Seq.slice s_dst (v pos - v offset) (v pos - v offset + v i32) /\
   //                                   Seq.slice s_src 0 (v i32 + 1) `Seq.equal` Seq.slice s_dst (v pos - v offset) (v pos - v offset + v i32 + 1) /\
   //                                   // B.modifies (B.loc_buffer_from_to b (pos - offset) (pos - offset + i32 + 1)) h0 h2 /\
   //                                   True );
   //                           assume (B.modifies (B.loc_buffer_from_to b (pos - offset) (pos - offset + i32)) h0 h2);
   //                           assume (B.modifies (B.loc_buffer_from_to b (pos - offset + 1) (pos - offset + i32)) h0 h2);
   //                           // assert (B.modifies (B.loc_buffer_from_to b (pos - offset) (pos - offset + i32 + 1ul)) h0 h2);
   //                           admit ()
   //                           // B.modifies_loc_buffer_from_to_intro
   //              );

   // (* Prf *) assert (
   //   let s = B.as_seq h b in
   //   let sub1:Seq.lseq byte 9 = Seq.create 9 0uy in
   //   let sub2:Seq.lseq byte 9 = Seq.create 9 1uy in
   //   let s1 = Seq.replace_subseq s (v pos - 9) (v pos) sub1 in
   //   let s2 = Seq.replace_subseq s (v pos - 9) (v pos) sub2 in
   //   Seq.lemma_index_create 9 0uy 0;
   //   Seq.lemma_index_create 9 1uy 0;
   //   s1.[v pos - 9] == 0uy /\
   //   s2.[v pos - 9] == 1uy /\

   //   (* diseq for seqs *)
   //   sub1 =!= sub2 /\
   //   ~ (s1 `Seq.equal` s2) /\

   //   (* rel *)
   //   s1 `rel` s2 /\
   //   ~ (s1 `IB.immutable_preorder byte` s2) /\
   //   ~ ( (s1 `rel` s2) <==> (s1 `IB.immutable_preorder byte` s2) ) /\
   //   rel =!= (IB.immutable_preorder byte)
   //   );

   //   assert ( MB.rrel_rel_always_compatible rrel rel);

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
