module DICE.Definitions

module HS = FStar.HyperStack

module I = Lib.IntTypes
module B = LowStar.Buffer

module S = Spec.Hash.Definitions
module H = Hacl.Hash.Definitions


type dice_hash_alg = a:S.hash_alg{a =!= S.MD5 /\ a =!= S.SHA2_224}

inline_for_extraction
let alg : dice_hash_alg = S.SHA2_256

inline_for_extraction noextract
let dice_hash (alg:dice_hash_alg) : H.hash_st alg =
  match alg with
  | S.SHA2_256 -> Hacl.Hash.SHA2.hash_256
  | S.SHA2_384 -> Hacl.Hash.SHA2.hash_384
  | S.SHA2_512 -> Hacl.Hash.SHA2.hash_512
  | S.SHA1     -> Hacl.Hash.SHA1.legacy_hash

inline_for_extraction noextract
let dice_hmac (alg:dice_hash_alg) : Hacl.HMAC.compute_st alg =
  match alg with
  | S.SHA2_256 -> Hacl.HMAC.compute_sha2_256
  | S.SHA2_384 -> Hacl.HMAC.compute_sha2_384
  | S.SHA2_512 -> Hacl.HMAC.compute_sha2_512
  | S.SHA1     -> Hacl.HMAC.legacy_compute_sha1

unfold let digest_len = H.hash_len alg

unfold let digest_t = H.hash_t alg

unfold let max_input_len = S.max_input_length alg

unfold let hashable_len = i:I.size_t{0 < I.v i /\ I.v i <= max_input_len}

unfold let signature_t = B.lbuffer I.uint8 64
unfold let key_t = B.lbuffer I.uint8 32


unfold let cdi_len = digest_len



noeq
type riot_header_t = {
  binary_size : hashable_len;
  binary_hash : digest_t;
  header_sig  : signature_t;
  
  binary      : B.lbuffer I.uint8 (I.v binary_size);
  pubkey      : (k:key_t{
    B.(all_disjoint [
        B.loc_buffer binary_hash;
        B.loc_buffer header_sig;
        B.loc_buffer binary;
        B.loc_buffer k ])
  });
}

let riot_header_locs (rh:riot_header_t) : GTot (list B.loc) = [
  B.loc_buffer rh.binary_hash;
  B.loc_buffer rh.header_sig;
  B.loc_buffer rh.binary;
  B.loc_buffer rh.pubkey
]

let contains_riot_header (h:HS.mem) (rh:riot_header_t) =
  B.all_live h [
    B.buf rh.binary_hash;
    B.buf rh.header_sig;
    B.buf rh.binary;
    B.buf rh.pubkey
  ]
