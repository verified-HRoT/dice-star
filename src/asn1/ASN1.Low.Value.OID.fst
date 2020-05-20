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

open IB

// let test (b:ibuffer int) (s:G.erased (Seq.seq int))
// : Lemma
//   (requires witnessed b (cpred (G.reveal s)))
//   (ensures witnessed b (seq_eq s))
// = assert (0 + v (len b) <= length b);
//   assert (mgsub (immutable_preorder int) b 0ul (len b) == b);
//   witnessed_functorial b b 0ul (len b) (cpred (G.reveal s)) (seq_eq (s))

let test
  (len: size_t)
  (seq: lbytes (v len))
  (ib: IB.libuffer byte (v len) seq {IB.recallable ib /\ IB.frameOf ib == HS.root} )
: HST.St (unit)
= IB.recall ib;
  IB.recall_contents ib seq;
  let x = 1 in
()

(* FIXME: Notes about `IB` and Ghost seq:
   NOTE: `IB.cpred` vs `IB.seq_eq`, `IB.recall_contents` vs `IB.recall_value`
   We may want to use the following `oid_seq` to represent a
   immutable buffer, but now the `IB` library is not universally
   using ghost seq, because HACL* is dependent on the legacy `IB`
   which is using (witnessing, recalling over) (total) seq. The
   allocation function `IB.igcmalloc_of_list` is one of those
   blocked by HACL*.
*)
noeq
type oid_buffer_t = {
  oid_len: asn1_value_int32_of_type OID;
  oid_seq: G.erased (lbytes (v oid_len));
  oid_buf: ib: IB.libuffer byte (v oid_len) (G.reveal oid_seq) {
           B.frameOf ib == HS.root /\
           B.recallable ib
  }
}

let oid_RIOT_as_buffer                     = IB.igcmalloc_of_list HS.root oid_RIOT
let oid_AT_CN_as_buffer                    = IB.igcmalloc_of_list HS.root oid_AT_CN
let oid_AT_COUNTRY_as_buffer               = IB.igcmalloc_of_list HS.root oid_AT_COUNTRY
let oid_AT_ORGANIZATION_as_buffer          = IB.igcmalloc_of_list HS.root oid_AT_ORGANIZATION
let oid_CLIENT_AUTH_as_buffer              = IB.igcmalloc_of_list HS.root oid_CLIENT_AUTH
let oid_AUTHORITY_KEY_IDENTIFIER_as_buffer = IB.igcmalloc_of_list HS.root oid_AUTHORITY_KEY_IDENTIFIER
let oid_KEY_USAGE_as_buffer                = IB.igcmalloc_of_list HS.root oid_KEY_USAGE
let oid_EXTENDED_KEY_USAGE_as_buffer       = IB.igcmalloc_of_list HS.root oid_EXTENDED_KEY_USAGE
let oid_BASIC_CONSTRAINTS_as_buffer        = IB.igcmalloc_of_list HS.root oid_BASIC_CONSTRAINTS

// let oid_DIGEST_ALG_SHA224_as_buffer: oid_buffer_t
// = { oid_len = 9ul;
//     oid_seq = G.hide (Seq.createL oid_DIGEST_ALG_SHA224);
//     oid_buf = IB.igcmalloc_of_list HS.root oid_DIGEST_ALG_SHA224 }
let oid_DIGEST_ALG_SHA224_as_buffer
= IB.igcmalloc_of_list HS.root oid_DIGEST_ALG_SHA224

// let oid_DIGEST_ALG_SHA256_as_buffer: oid_buffer_t
// = { oid_len = 9ul;
//     oid_seq = G.hide (Seq.createL oid_DIGEST_ALG_SHA256);
//     oid_buf = IB.igcmalloc_of_list HS.root oid_DIGEST_ALG_SHA256 }
let oid_DIGEST_ALG_SHA256_as_buffer
= IB.igcmalloc_of_list HS.root oid_DIGEST_ALG_SHA256

// let oid_DIGEST_ALG_SHA384_as_buffer: oid_buffer_t
// = { oid_len = 9ul;
//     oid_seq = G.hide (Seq.createL oid_DIGEST_ALG_SHA384);
//     oid_buf = IB.igcmalloc_of_list HS.root oid_DIGEST_ALG_SHA384 }
let oid_DIGEST_ALG_SHA384_as_buffer
= IB.igcmalloc_of_list HS.root oid_DIGEST_ALG_SHA384

// let oid_DIGEST_ALG_SHA512_as_buffer: oid_buffer_t
// = { oid_len = 9ul;
//     oid_seq = G.hide (Seq.createL oid_DIGEST_ALG_SHA512);
//     oid_buf = IB.igcmalloc_of_list HS.root oid_DIGEST_ALG_SHA512 }
let oid_DIGEST_ALG_SHA512_as_buffer
= IB.igcmalloc_of_list HS.root oid_DIGEST_ALG_SHA512

(* NOTE: We may remove this if we are not implementing the parser. *)
noextract
let list_of_oid_buffers
= [ oid_RIOT_as_buffer;
    oid_AT_CN_as_buffer;
    oid_AT_COUNTRY_as_buffer;
    oid_AT_ORGANIZATION_as_buffer;
    oid_CLIENT_AUTH_as_buffer;
    oid_AUTHORITY_KEY_IDENTIFIER_as_buffer;
    oid_KEY_USAGE_as_buffer;
    oid_EXTENDED_KEY_USAGE_as_buffer;
    oid_BASIC_CONSTRAINTS_as_buffer;
    oid_DIGEST_ALG_SHA224_as_buffer;
    oid_DIGEST_ALG_SHA256_as_buffer;
    oid_DIGEST_ALG_SHA384_as_buffer;
    oid_DIGEST_ALG_SHA512_as_buffer
]
let known_oids_as_buffer = IB.igcmalloc_of_list HS.root list_of_oid_buffers


(* FIXME: A workaround
   To not extract any (total) seq, we split the `oid_buffer_t` into three
   functions, all of them take an `oid: oid_t`, returns the corresponding
   len, (total) seq and ibuffer. The (total) seq will be only used in the
   `IB.recall_contents` lemma, and the function returns the (total) seq
   will be marded as `noextract`.
*)

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
  | OID_DIGEST_SHA224            -> oid_DIGEST_ALG_SHA224_as_buffer
  | OID_DIGEST_SHA256            -> oid_DIGEST_ALG_SHA256_as_buffer
  | OID_DIGEST_SHA384            -> oid_DIGEST_ALG_SHA384_as_buffer
  | OID_DIGEST_SHA512            -> oid_DIGEST_ALG_SHA512_as_buffer

let len_of_oid_buffer
  (oid: oid_t)
: Tot (len: asn1_value_int32_of_type OID
      { v len == B.length (oid_buffer_of_oid oid) })
      // { v len == Seq.length (normalize_term (oid_seq_of oid)) })
= match oid with
  | OID_DIGEST_SHA224 -> 9ul
  | OID_DIGEST_SHA256 -> 9ul
  | OID_DIGEST_SHA384 -> 9ul
  | OID_DIGEST_SHA512 -> 9ul
  | _ -> admit()

noextract
let seq_of_oid_buffer
  (oid: oid_t)
: Tot (s: bytes {List.mem s known_oids_as_seq /\
                 B.witnessed (oid_buffer_of_oid oid) (IB.cpred s)})
= oid_seq_of oid

(*)
inline_for_extraction
let blit_from_ib
  (src_seq: G.erased bytes) (* How to erase it? *)
  (src: IB.ibuffer byte {B.frameOf src == HS.root /\ B.recallable src})
  (src_from src_to: size_t)
  (#rrel #rel: _)
  (dst: B.mbuffer byte rrel rel)
  (dst_pos: size_t)
: HST.Stack unit
  (requires (fun h ->
    B.live h dst /\
    v src_from <= v src_to /\ v src_to <= B.length src /\
    v dst_pos + (v src_to - v src_from) <= B.length dst /\
    // U32.v src_from <= U32.v src_to /\ U32.v src_to <= BY.length src /\
    // U32.v dst_pos + (U32.v src_to - U32.v src_from) <= B.length dst /\
    writable dst (v dst_pos) (v dst_pos + (v src_to - v src_from)) h
  ))
  (ensures (fun h _ h' ->
    B.modifies (B.loc_buffer_from_to dst dst_pos (dst_pos + (src_to - src_from))) h h' /\
    Seq.slice (B.as_seq h' dst) (v dst_pos) (v dst_pos + (v src_to - v src_from)) == Seq.slice (B.as_seq h src) (v src_from) (v src_to)
  ))
= let h0 = HST.get () in
  HST.push_frame ();
  let h1 = HST.get () in
  let bi: B.pointer size_t = B.alloca 0ul 1ul in
  let h2 = HST.get () in
  let len = src_to - src_from in
  C.Loops.do_while
    (fun h stop ->
      B.modifies (B.loc_union (B.loc_region_only true (HS.get_tip h1)) (B.loc_buffer_from_to dst dst_pos (dst_pos + len))) h2 h /\
      B.live h bi /\ (
      let i = Seq.index (B.as_seq h bi) 0 in
      v i <= v len /\
      writable dst (v dst_pos) (v dst_pos + v len) h /\
      Seq.slice (B.as_seq h dst) (v dst_pos) (v dst_pos + v i) `Seq.equal` Seq.slice (B.as_seq h src) (v src_from) (v src_from + v i) /\
      (stop == true ==> i == len)
    ))
    (fun _ ->
      let i = B.index bi 0ul in
      if i = len
      then true
      else begin
        B.recall src;
        IB.recall_value src src_seq;
        let x = B.index src (src_from + i) in
        mbuffer_upd dst (Ghost.hide (v dst_pos)) (Ghost.hide (v dst_pos + v len)) (dst_pos + i) x;
        let i': size_t = i + 1ul in
        B.upd bi 0ul i';
        let h' = HST.get () in
        Seq.lemma_split (Seq.slice (B.as_seq h' dst) (v dst_pos) (v dst_pos + v i')) (v i);
        i' = len
      end
    )
    ;
  HST.pop_frame ()
#pop-options
*)

#restart-solver
#push-options "--query_stats --z3rlimit 16"
inline_for_extraction
let serialize32_asn1_oid_backwards
  (len: asn1_value_int32_of_type OID)
: Tot (serializer32_backwards (serialize_asn1_oid (v len)))
= fun (oid: oid_t { Seq.length (oid_seq_of oid) == v len })
    (#rrel #rel: _)
    (b: B.mbuffer byte rrel rel)
    (pos: size_t)
-> (* Prf *) serialize_asn1_oid_unfold (v len) oid;
   (* Prf *) serialize_asn1_oid_size (v len) oid;
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
: Tot (tg: (the_asn1_type OID & asn1_value_int32_of_type OID)
      { tg == parser_tag_of_oid x })
= (OID, len_of_oid_buffer x)

#push-options "--query_stats --z3rlimit 32"
inline_for_extraction
let synth_asn1_oid_V_inverse_impl
  (tg: (the_asn1_type OID & asn1_value_int32_of_type OID))
  (value': refine_with_tag parser_tag_of_oid tg)
: Tot (value: datatype_of_asn1_type OID
      { length_of_oid value == v (snd tg) /\
        value == synth_asn1_oid_V_inverse tg value' })
= value'
#pop-options

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
