module RIoT.Core.Lemmas

module B = LowStar.Buffer
module IB = LowStar.ImmutableBuffer
module HS  = FStar.HyperStack
module HST = FStar.HyperStack.ST

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0 --using_facts_from '* -FStar.Tactics -FStar.Reflection'"

let lemma_riot_modifies
  (pub_t sec_t: Type0)
  (init_pub: pub_t) (init_sec: sec_t)
  (h0 hf: HS.mem)
  (deviceID_pub   : B.buffer pub_t)
  (aliasKey_pub   : B.buffer pub_t)
  (aliasKey_priv  : B.buffer sec_t)
  (deviceIDCSR_buf: B.buffer pub_t)
  (aliasKeyCRT_buf: B.buffer pub_t)
  (hs0 hs01 hs02 hs1 hs2 hs3 hsf: HS.mem)
  (_deviceID_priv : B.buffer sec_t)
  (_authKeyID     : B.buffer pub_t)
: Lemma
  (requires HS.fresh_frame h0 hs0 /\ HS.get_tip hs0 == HS.get_tip hsf /\ HS.popped hsf hf /\
            B.alloc_post_mem_common _deviceID_priv hs0  hs01 (Seq.create 32 init_sec) /\ B.frameOf _deviceID_priv == HS.get_tip hs0  /\
            B.alloc_post_mem_common _authKeyID     hs01 hs02 (Seq.create 20 init_pub) /\ B.frameOf _authKeyID     == HS.get_tip hs01 /\
            B.modifies (B.loc_buffer deviceID_pub   `B.loc_union`
                        B.loc_buffer _deviceID_priv `B.loc_union`
                        B.loc_buffer aliasKey_pub   `B.loc_union`
                        B.loc_buffer aliasKey_priv  `B.loc_union`
                        B.loc_buffer _authKeyID) hs02 hs1 /\
            B.modifies (B.loc_buffer deviceID_pub   `B.loc_union`
                        B.loc_buffer _deviceID_priv `B.loc_union`
                        B.loc_buffer aliasKey_pub   `B.loc_union`
                        B.loc_buffer aliasKey_priv  `B.loc_union`
                        B.loc_buffer _authKeyID     `B.loc_union`
                        B.loc_buffer deviceIDCSR_buf
                        ) hs1 hs2 /\
            B.modifies (B.loc_buffer deviceID_pub    `B.loc_union`
                        B.loc_buffer _deviceID_priv  `B.loc_union`
                        B.loc_buffer aliasKey_pub    `B.loc_union`
                        B.loc_buffer aliasKey_priv   `B.loc_union`
                        B.loc_buffer _authKeyID      `B.loc_union`
                        B.loc_buffer deviceIDCSR_buf `B.loc_union`
                        B.loc_buffer aliasKeyCRT_buf
                        ) hs2 hs3 /\
            hs3 == hsf)
  (ensures B.(modifies (loc_buffer deviceID_pub    `loc_union`
                        loc_buffer aliasKey_pub    `loc_union`
                        loc_buffer aliasKey_priv   `loc_union`
                        loc_buffer deviceIDCSR_buf `loc_union`
                        loc_buffer aliasKeyCRT_buf) h0 hf) )
= ()
