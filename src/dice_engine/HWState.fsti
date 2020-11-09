module HWState

open FStar.Integers
open FStar.HyperStack.ST

module G = FStar.Ghost
module HS = FStar.HyperStack
module B = LowStar.Buffer

open DICE.Engine.Definitions

#set-options "--__temp_no_proj HWState"

type mbuffer (a:Type0) (len:nat) =
  b:B.lbuffer a len{B.frameOf b == HS.root /\ B.recallable b}

type mpointer (a:Type0) (rel:B.srel a) =
  b:B.mbuffer a rel rel{B.frameOf b == HS.root /\ B.recallable b /\ B.length b == 1}

val t : Type0

val t_rel : B.srel (G.erased t)

noeq
type l0_image_t = {
  l0_image_header_size : signable_len;
  l0_image_header      : mbuffer byte_sec (v l0_image_header_size);
  l0_image_header_sig  : mbuffer byte_sec 64;
  l0_binary_size       : hashable_len;
  l0_binary            : mbuffer byte_sec (v l0_binary_size);
  l0_binary_hash       : mbuffer byte_sec (v digest_len);
  l0_image_auth_pubkey : b:mbuffer byte_sec 32{
    B.(all_disjoint [loc_buffer l0_image_header;
                     loc_buffer l0_image_header_sig;
                     loc_buffer l0_binary;
                     loc_buffer l0_binary_hash;
                     loc_buffer b ])
  }
}

noeq
type state = {
  ghost_state : mpointer (G.erased t) t_rel;

  cdi : mbuffer byte_sec (v digest_len);

  l0 : img:l0_image_t{
    B.(all_disjoint [loc_buffer ghost_state;
                     loc_buffer cdi;
                     loc_buffer img.l0_image_header;
                     loc_buffer img.l0_image_header_sig;
                     loc_buffer img.l0_binary;
                     loc_buffer img.l0_binary_hash;
                     loc_buffer img.l0_image_auth_pubkey ])
  }
}
