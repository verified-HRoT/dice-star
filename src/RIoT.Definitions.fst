module RIoT.Definitions

module HS = FStar.HyperStack

module I = Lib.IntTypes
module B = LowStar.Buffer

module S = Spec.Hash.Definitions
module H = Hacl.Hash.Definitions

(*
 * Some common definitions used in the RIoT code
 *)

#set-options "--__temp_no_proj RIoT.Definitions"

(* ZT: restrict it to `SHA2_256` for convenience,
       because `Hacl.Curve25519` only support it *)
type riot_hash_alg = a:S.hash_alg{a == S.SHA2_256}

inline_for_extraction
let alg : riot_hash_alg = S.SHA2_256

inline_for_extraction noextract
let riot_hash (alg:riot_hash_alg) : H.hash_st alg =
  match alg with
  | S.SHA2_256 -> Hacl.Hash.SHA2.hash_256
  | S.SHA2_384 -> Hacl.Hash.SHA2.hash_384
  | S.SHA2_512 -> Hacl.Hash.SHA2.hash_512
  | S.SHA1     -> Hacl.Hash.SHA1.legacy_hash

inline_for_extraction noextract
let riot_hmac (alg:riot_hash_alg) : Hacl.HMAC.compute_st alg =
  match alg with
  | S.SHA2_256 -> Hacl.HMAC.compute_sha2_256
  | S.SHA2_384 -> Hacl.HMAC.compute_sha2_384
  | S.SHA2_512 -> Hacl.HMAC.compute_sha2_512
  | S.SHA1     -> Hacl.HMAC.legacy_compute_sha1

unfold let digest_len = H.hash_len alg

unfold type digest_t = H.hash_t alg

unfold type hashable_len = i:I.size_t{0 < I.v i /\ I.v i <= S.max_input_length alg}

unfold let cdi_len = digest_len


/// Some types used in the public key verification of the RIoT header

unfold type signature_t = B.lbuffer I.uint8 64
unfold type key_t = B.lbuffer I.uint8 32

noeq
type ext_t = {
   // riot_oid: ;
}

(* ZT: will revise them *)
noeq
type cert_t = {
  tbs: B.lbuffer I.uint8 32;
  sig: s: signature_t{
    B.disjoint tbs s
  }
}

unfold
let contains_cert h cert =
  B.live h cert.tbs /\
  B.live h cert.sig

unfold
let get_cert_loc_l cert = [
  B.loc_buffer cert.tbs;
  B.loc_buffer cert.sig
]

noeq
type riot_out_t = {
     // alias_public_key    : B.lbuffer uint8 32;
     // alias_private_key   : B.lbuffer uint8 32;
     deviceID_public_key : B.lbuffer I.uint8 32;
     deviceID_cert       : cert: cert_t{
       B.(all_disjoint
            ([loc_buffer deviceID_public_key]
            @(get_cert_loc_l cert)))
     }
}

unfold
let contains_riot_out (h: HS.mem) (rout: riot_out_t) =
  // B.live h rout.alias_public_key /\
  // B.live h rout.alias_private_key /\
  B.live h rout.deviceID_public_key /\
  h `contains_cert` rout.deviceID_cert

unfold
let get_riot_out_loc_l rout = [
   // B.loc_buffer rout.alias_public_key;
   // B.loc_buffer rout.alias_private_key;
   B.loc_buffer rout.deviceID_public_key
] @ (get_cert_loc_l rout.deviceID_cert)
