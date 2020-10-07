module RIoT.Core.Lemmas

module B = LowStar.Buffer
module HS  = FStar.HyperStack
module HST = FStar.HyperStack.ST

#set-options "--z3rlimit 16 --fuel 0 --ifuel 0"
let f
  (b1 b2: B.lbuffer UInt8.t 1)
: HST.Stack unit
  (requires fun h -> B.live h b1 /\ B.live h b2 /\ B.disjoint b1 b2)
  (ensures fun h0 _ h1 -> True)
= let h0 = HST.get () in
  HST.push_frame ();
    let hs0 = HST.get () in
    let b3 = B.alloca 0uy 1ul in
    let b4 = B.alloca 0uy 1ul in
    let hs1 = HST.get () in

    B.upd b1 0ul 0uy;
    B.upd b2 0ul 0uy;
    let hs2 = HST.get () in

    B.upd b3 0ul 1uy;
    B.upd b4 0ul 1uy;

    let hs3 = HST.get () in
    assert (B.modifies (B.loc_buffer b1 `B.loc_union`
                        B.loc_buffer b2 `B.loc_union`
                        B.loc_buffer b3 `B.loc_union`
                        B.loc_buffer b4) h0 hs3);

  HST.pop_frame ();
  let hf = HST.get () in
  assert (B.modifies (B.loc_buffer b1 `B.loc_union`
                      B.loc_buffer b2) h0 hf);
  assert ((forall (r:HS.rid).
              HS.get_hmap h0 `Map.contains` r /\ HS.get_hmap hf `Map.contains` r
              ==> Heap.equal_dom (HS.get_hmap h0 `Map.sel` r) (HS.get_hmap hf `Map.sel` r)));
  assert (HST.equal_domains h0 hf)

module U32 = FStar.UInt32
module U8 = FStar.UInt8

#set-options "--z3rlimit 256 --fuel 0 --ifuel 0"
let lemma_help
  (pub_t sec_t: Type0)
  (h0 hs0 hsf hf: HS.mem)
  (in1: B.buffer sec_t) (in2: B.buffer sec_t) (in3: B.buffer sec_t) (in4: B.buffer sec_t)
  (out1: B.buffer pub_t) (out2: B.buffer sec_t) (out3: B.buffer pub_t) (out4: B.buffer pub_t)
  (hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 hs12 hs13 hs14: HS.mem)
  (_bl1: UInt32.t) (_b1: B.lbuffer pub_t (U32.v _bl1)) (_bv1: pub_t)
  (_bl2: UInt32.t) (_b2: B.lbuffer sec_t (U32.v _bl2)) (_bv2: sec_t)
  (_bl3: UInt32.t) (_b3: B.lbuffer sec_t (U32.v _bl3)) (_bv3: sec_t)
  (_bl4: UInt32.t) (_b4: B.lbuffer pub_t (U32.v _bl4)) (_bv4: pub_t)
  (_bl5: UInt32.t) (_b5: B.lbuffer pub_t (U32.v _bl5)) (_bv5: pub_t)
  (_bl6: UInt32.t) (_b6: B.lbuffer pub_t (U32.v _bl6)) (_bv6: pub_t)
: Lemma
  (requires
            B.all_live h0 [B.buf in1; B.buf in2; B.buf in3; B.buf in4;
                           B.buf out1; B.buf out2; B.buf out3; B.buf out4] /\
            B.all_disjoint [B.loc_buffer in1; B.loc_buffer in2; B.loc_buffer in3; B.loc_buffer in4;
                            B.loc_buffer out1; B.loc_buffer out2; B.loc_buffer out3; B.loc_buffer out4] /\
            HS.fresh_frame h0 hs0 /\ HS.get_tip hs0 == HS.get_tip hsf /\ HS.popped hsf hf /\
            B.alloc_post_mem_common _b1 hs0 hs1 (Seq.create (UInt32.v _bl1) _bv1) /\ B.frameOf _b1 == HS.get_tip hs0 /\
            B.alloc_post_mem_common _b2 hs1 hs2 (Seq.create (UInt32.v _bl2) _bv2) /\ B.frameOf _b2 == HS.get_tip hs1 /\
            B.alloc_post_mem_common _b3 hs2 hs3 (Seq.create (UInt32.v _bl3) _bv3) /\ B.frameOf _b3 == HS.get_tip hs2 /\
            B.alloc_post_mem_common _b4 hs3 hs4 (Seq.create (UInt32.v _bl4) _bv4) /\ B.frameOf _b4 == HS.get_tip hs3 /\

            (* Derive DeviceID *)
            B.modifies (B.loc_buffer _b1 `B.loc_union` B.loc_buffer _b2) hs4 hs5 /\

            (* Derive AliasKey *)
            B.modifies (B.loc_buffer out1 `B.loc_union` B.loc_buffer out2) hs5 hs6 /\

            (* Classify DeviceID Public Key *)
            B.modifies (B.loc_buffer _b3) hs6 hs7 /\

            (* Derive AliasCRT_AuthKeyID *)
            B.modifies (B.loc_buffer _b4) hs7 hs8 /\

            (* Allocate `deviceIDCRI_buf` *)
            B.alloc_post_mem_common _b5 hs8 hs9 (Seq.create (UInt32.v _bl5) _bv5) /\ B.frameOf _b5 == HS.get_tip hs8 /\

            (* Write `deviceIDCRI_buf` *)
            B.modifies (B.loc_buffer _b5) hs9 hs10 /\

            (* Write `deviceIDCSR_buf` *)
            B.modifies (B.loc_buffer out3) hs10 hs11 /\

            (* Allocate `aliasKeyTBS_buf` *)
            B.alloc_post_mem_common _b6 hs11 hs12 (Seq.create (UInt32.v _bl6) _bv6) /\ B.frameOf _b6 == HS.get_tip hs11 /\

            (* Write `aliasKeyTBS_buf` *)
            B.modifies (B.loc_buffer _b6) hs12 hs13 /\

            (* Write `aliasKeyCRT_buf` *)
            B.modifies (B.loc_buffer out4) hs13 hs14 /\

            hs14 == hsf
            )
  (ensures
    B.modifies (B.loc_buffer out1 `B.loc_union`
                B.loc_buffer out2 `B.loc_union`
                B.loc_buffer out3 `B.loc_union`
                B.loc_buffer out4) h0 hf /\

    B.as_seq hs4  in1  == B.as_seq h0 in1 /\ // cdi
    B.as_seq hs4  in3  == B.as_seq h0 in3 /\ // lbl device

    B.as_seq hs5  in1  == B.as_seq h0 in1 /\ // cdi
    B.as_seq hs5  in2  == B.as_seq h0 in2 /\ // fwid
    B.as_seq hs5  in4  == B.as_seq h0 in4 /\ // lbl alias

    B.as_seq hs6  out1 == B.as_seq hf out1 /\
    B.as_seq hs6  out2 == B.as_seq hf out2 /\
    B.as_seq hs11 out3 == B.as_seq hf out3 /\
    B.as_seq hs14 out4 == B.as_seq hf out4 /\
    True
  )
=
  B.modifies_trans B.loc_none h0 hs0 B.loc_none hs1;
  B.modifies_trans B.loc_none h0 hs1 B.loc_none hs2;
  B.modifies_trans B.loc_none h0 hs2 B.loc_none hs3;
  B.modifies_trans B.loc_none h0 hs3 B.loc_none hs4;

  B.modifies_buffer_elim in1 B.loc_none h0 hs4;
  B.modifies_buffer_elim in3 B.loc_none h0 hs4;

(* hs4 --> hs5 *)
  B.modifies_trans B.loc_none h0 hs4 (
    B.loc_buffer _b1 `B.loc_union`
    B.loc_buffer _b2
  ) hs5;
  B.modifies_buffer_elim in1 (B.loc_buffer out1 `B.loc_union` B.loc_buffer out2) h0 hs5;
  B.modifies_buffer_elim in2 (B.loc_buffer out1 `B.loc_union` B.loc_buffer out2) h0 hs5;
  B.modifies_buffer_elim in4 (B.loc_buffer out1 `B.loc_union` B.loc_buffer out2) h0 hs5;

(* hs5 --> hs6 *)
  B.modifies_trans (
    B.loc_buffer _b1 `B.loc_union`
    B.loc_buffer _b2
  ) h0 hs5 (
    B.loc_buffer out1 `B.loc_union`
    B.loc_buffer out2
  ) hs6;
  B.modifies_buffer_elim _b1 (B.loc_buffer out1 `B.loc_union` B.loc_buffer out2) hs5 hs6;
  B.modifies_buffer_elim _b2 (B.loc_buffer out1 `B.loc_union` B.loc_buffer out2) hs5 hs6;

(* hs6 --> hs7 *)
  B.modifies_trans (
    B.loc_buffer _b1 `B.loc_union`
    B.loc_buffer _b2 `B.loc_union`
    B.loc_buffer out1  `B.loc_union`
    B.loc_buffer out2
  ) h0 hs6 (
    B.loc_buffer _b3
  ) hs7;
  B.modifies_buffer_elim _b1 (B.loc_buffer _b3) hs6 hs7;
  B.modifies_buffer_elim _b2 (B.loc_buffer _b3) hs6 hs7;
  B.modifies_buffer_elim out1  (B.loc_buffer _b3) hs6 hs7;
  B.modifies_buffer_elim out2  (B.loc_buffer _b3) hs6 hs7;

(* hs7 --> hs8 *)
  B.modifies_trans (
    B.loc_buffer _b1 `B.loc_union`
    B.loc_buffer _b2 `B.loc_union`
    B.loc_buffer out1  `B.loc_union`
    B.loc_buffer out2  `B.loc_union`
    B.loc_buffer _b3
  ) h0 hs7 (
    B.loc_buffer _b4
  ) hs8;
  B.modifies_buffer_elim _b1 (B.loc_buffer _b4) hs7 hs8;
  B.modifies_buffer_elim _b2 (B.loc_buffer _b4) hs7 hs8;
  B.modifies_buffer_elim out1  (B.loc_buffer _b4) hs7 hs8;
  B.modifies_buffer_elim out2  (B.loc_buffer _b4) hs7 hs8;
  B.modifies_buffer_elim _b3 (B.loc_buffer _b4) hs7 hs8;

(* hs8 --> hs9 *)
  B.modifies_trans (
    B.loc_buffer _b1 `B.loc_union`
    B.loc_buffer _b2 `B.loc_union`
    B.loc_buffer out1  `B.loc_union`
    B.loc_buffer out2  `B.loc_union`
    B.loc_buffer _b3 `B.loc_union`
    B.loc_buffer _b4
  ) h0 hs8 B.loc_none hs9;
  B.modifies_buffer_elim _b1 B.loc_none hs8 hs9;
  B.modifies_buffer_elim _b2 B.loc_none hs8 hs9;
  B.modifies_buffer_elim out1  B.loc_none hs8 hs9;
  B.modifies_buffer_elim out2  B.loc_none hs8 hs9;
  B.modifies_buffer_elim _b3 B.loc_none hs8 hs9;
  B.modifies_buffer_elim _b4 B.loc_none hs8 hs9;

(* hs9 --> hs10 *)
  B.modifies_trans (
    B.loc_buffer _b1 `B.loc_union`
    B.loc_buffer _b2 `B.loc_union`
    B.loc_buffer out1  `B.loc_union`
    B.loc_buffer out2  `B.loc_union`
    B.loc_buffer _b3 `B.loc_union`
    B.loc_buffer _b4
  ) h0 hs9 (
    B.loc_buffer _b5
  ) hs10;
  B.modifies_buffer_elim _b1 (B.loc_buffer _b5) hs9 hs10;
  B.modifies_buffer_elim _b2 (B.loc_buffer _b5) hs9 hs10;
  B.modifies_buffer_elim out1  (B.loc_buffer _b5) hs9 hs10;
  B.modifies_buffer_elim out2  (B.loc_buffer _b5) hs9 hs10;
  B.modifies_buffer_elim _b3 (B.loc_buffer _b5) hs9 hs10;
  B.modifies_buffer_elim _b4 (B.loc_buffer _b5) hs9 hs10;


(* hs10 --> hs11 *)
  B.modifies_trans (
    B.loc_buffer _b1 `B.loc_union`
    B.loc_buffer _b2 `B.loc_union`
    B.loc_buffer out1  `B.loc_union`
    B.loc_buffer out2  `B.loc_union`
    B.loc_buffer _b3 `B.loc_union`
    B.loc_buffer _b4 `B.loc_union`
    B.loc_buffer _b5
  ) h0 hs10 (
    B.loc_buffer out3
  ) hs11;
  B.modifies_buffer_elim _b1 (B.loc_buffer out3) hs10 hs11;
  B.modifies_buffer_elim _b2 (B.loc_buffer out3) hs10 hs11;
  B.modifies_buffer_elim out1  (B.loc_buffer out3) hs10 hs11;
  B.modifies_buffer_elim out2  (B.loc_buffer out3) hs10 hs11;
  B.modifies_buffer_elim _b3 (B.loc_buffer out3) hs10 hs11;
  B.modifies_buffer_elim _b4 (B.loc_buffer out3) hs10 hs11;
  B.modifies_buffer_elim _b5 (B.loc_buffer out3) hs10 hs11;

(* hs11 --> hs12 *)
  B.modifies_trans (
    B.loc_buffer _b1 `B.loc_union`
    B.loc_buffer _b2 `B.loc_union`
    B.loc_buffer out1  `B.loc_union`
    B.loc_buffer out2  `B.loc_union`
    B.loc_buffer _b3 `B.loc_union`
    B.loc_buffer _b4 `B.loc_union`
    B.loc_buffer _b5 `B.loc_union`
    B.loc_buffer out3
  ) h0 hs11 B.loc_none hs12;
  B.modifies_buffer_elim _b1 B.loc_none hs11 hs12;
  B.modifies_buffer_elim _b2 B.loc_none hs11 hs12;
  B.modifies_buffer_elim out1  B.loc_none hs11 hs12;
  B.modifies_buffer_elim out2  B.loc_none hs11 hs12;
  B.modifies_buffer_elim _b3 B.loc_none hs11 hs12;
  B.modifies_buffer_elim _b4 B.loc_none hs11 hs12;
  B.modifies_buffer_elim _b5 B.loc_none hs11 hs12;
  B.modifies_buffer_elim out3  B.loc_none hs11 hs12;

(* hs12 --> hs13 *)
  B.modifies_trans (
    B.loc_buffer _b1 `B.loc_union`
    B.loc_buffer _b2 `B.loc_union`
    B.loc_buffer out1  `B.loc_union`
    B.loc_buffer out2  `B.loc_union`
    B.loc_buffer _b3 `B.loc_union`
    B.loc_buffer _b4 `B.loc_union`
    B.loc_buffer _b5 `B.loc_union`
    B.loc_buffer out3
  ) h0 hs12 (
    B.loc_buffer _b6
  ) hs13;
  B.modifies_buffer_elim _b1 (B.loc_buffer _b6) hs12 hs13;
  B.modifies_buffer_elim _b2 (B.loc_buffer _b6) hs12 hs13;
  B.modifies_buffer_elim out1  (B.loc_buffer _b6) hs12 hs13;
  B.modifies_buffer_elim out2  (B.loc_buffer _b6) hs12 hs13;
  B.modifies_buffer_elim _b3 (B.loc_buffer _b6) hs12 hs13;
  B.modifies_buffer_elim _b4 (B.loc_buffer _b6) hs12 hs13;
  B.modifies_buffer_elim _b5 (B.loc_buffer _b6) hs12 hs13;
  B.modifies_buffer_elim out3  (B.loc_buffer _b6) hs12 hs13;

(* hs13 --> hs14 *)
  B.modifies_trans (
    B.loc_buffer _b1 `B.loc_union`
    B.loc_buffer _b2 `B.loc_union`
    B.loc_buffer out1  `B.loc_union`
    B.loc_buffer out2  `B.loc_union`
    B.loc_buffer _b3 `B.loc_union`
    B.loc_buffer _b4 `B.loc_union`
    B.loc_buffer _b5 `B.loc_union`
    B.loc_buffer out3  `B.loc_union`
    B.loc_buffer _b6
  ) h0 hs13 (
    B.loc_buffer out4
  ) hs14;
  B.modifies_buffer_elim _b1 (B.loc_buffer out4) hs13 hs14;
  B.modifies_buffer_elim _b2 (B.loc_buffer out4) hs13 hs14;
  B.modifies_buffer_elim out1  (B.loc_buffer out4) hs13 hs14;
  B.modifies_buffer_elim out2  (B.loc_buffer out4) hs13 hs14;
  B.modifies_buffer_elim _b3 (B.loc_buffer out4) hs13 hs14;
  B.modifies_buffer_elim _b4 (B.loc_buffer out4) hs13 hs14;
  B.modifies_buffer_elim _b5 (B.loc_buffer out4) hs13 hs14;
  B.modifies_buffer_elim out3  (B.loc_buffer out4) hs13 hs14;
  B.modifies_buffer_elim _b6 (B.loc_buffer out4) hs13 hs14;

(* FIXME: This can be proved with 256-512 z3rlimits *)
  assume (B.modifies ((B.loc_all_regions_from false (HS.get_tip hs0)) `B.loc_union`
                      (B.loc_buffer out1 `B.loc_union`
                       B.loc_buffer out2 `B.loc_union`
                       B.loc_buffer out3 `B.loc_union`
                       B.loc_buffer out4)) hs0 hsf);

  B.modifies_fresh_frame_popped h0 hs0 (
    B.loc_buffer out1 `B.loc_union`
    B.loc_buffer out2 `B.loc_union`
    B.loc_buffer out3 `B.loc_union`
    B.loc_buffer out4
  ) hsf hf;

()

(*
   What's the difference between `B.modifies_fresh_frame_popped` and `B.modifies_remove_fresh_frame`?
*)

// let lemma_equal_domains
//   (a: Type0)
//   (h0 hs0 hsf hf: HS.mem)
//   (_bl1: UInt32.t) (_b1: B.lbuffer a (U32.v _bl1)) (_bv1: a)
// : Lemma
//   (requires
//     HS.fresh_frame h0 hs0 /\ HS.get_tip hs0 == HS.get_tip hsf /\ HS.popped hsf hf /\
//     B.alloc_post_mem_bommon _b1 hs0 hsf (Seq.create (UInt32.v _bl1) _bv1) /\ B.frameOf _b1 == HS.get_tip hs0)
//   (ensures
//     HS.get_tip h0 == HS.get_tip hf /\
//     Set.equal (Map.domain (HS.get_hmap h0)) (Map.domain (HS.get_hmap hf)) /\
//     HST.same_refs_in_all_regions h0 hf)
// = admit ()

