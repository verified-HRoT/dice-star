module DICE.Definitions

module HS = FStar.HyperStack

module I = Lib.IntTypes
module B = LowStar.Buffer

module S = Spec.Hash.Definitions
module H = Hacl.Hash.Definitions

open Lib.IntTypes

(*
 * Some common definitions used in the DICE code
 *)

#set-options "--__temp_no_proj DICE.Definitions"

let byte_sec = uint8
let byte_pub = pub_uint8

let bytes_sec = Seq.seq I.uint8
let bytes_pub = Seq.seq I.pub_uint8

let lbytes_sec = Seq.lseq I.uint8
let lbytes_pub = Seq.lseq I.pub_uint8

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

unfold type digest_t = H.hash_t alg

unfold type hashable_len = i: size_t {0 < v i /\ v i <= S.max_input_length alg}
unfold type signable_len = i: size_t {64 + v i <= max_size_t}
unfold let cdi_len = digest_len


/// Some types used in the public key verification of the RIoT header

unfold type signature_t = B.lbuffer I.uint8 64
unfold type key_t = B.lbuffer I.uint8 32

noeq
type image_t = {
  header_size : signable_len;
  image_header: B.lbuffer byte_sec (v header_size);
  image_hash  : digest_t;
  header_sig  : signature_t;
  image_size  : hashable_len;
  image_base  : image_base: B.buffer byte_sec
                { B.length image_base == v image_size };
(* NOTE: This pubkey is not part of the image *)
  pubkey      : pubkey: key_t
                { B.all_disjoint [B.loc_buffer image_header;
                                  B.loc_buffer image_hash;
                                  B.loc_buffer header_sig;
                                  B.loc_buffer image_base;
                                  B.loc_buffer pubkey] }
  }

let contains_image (h:HS.mem) (image:image_t) =
  B.all_live h [
    B.buf image.header_sig;
    B.buf image.image_header;
    B.buf image.image_hash;
    B.buf image.image_base;
    B.buf image.pubkey
  ]

let locs_of_image (image: image_t) =
  [B.loc_buffer image.image_header;
   B.loc_buffer image.image_hash;
   B.loc_buffer image.header_sig;
   B.loc_buffer image.image_base;
   B.loc_buffer image.pubkey]

open Lib.ByteBuffer
module S = Spec.Hash.Definitions
module Ed25519 = Hacl.Ed25519

let is_valid_image
  (pubkey: lbytes_sec 32)
  (image: bytes_sec {0 < Seq.length image /\ Seq.length image <= S.max_input_length alg})
  (image_hash: lbytes_sec 32)
  (image_header: bytes_sec {Seq.length image_header + 64<= max_size_t})
  (header_sig: lbytes_sec 64)
: Type0
= Spec.Ed25519.verify
    (* key *) pubkey
    (* msg *) image_header
    (* sig *) header_sig /\
  image_hash == Spec.Agile.Hash.hash alg image

let is_valid_image_st
  (image: image_t)
  (h: HS.mem)
: Type0
= Spec.Ed25519.verify
    (* key *) (B.as_seq h image.pubkey)
    (* msg *) (B.as_seq h image.image_header)
    (* sig *) (B.as_seq h image.header_sig) /\
  B.as_seq h image.image_hash ==
  Spec.Agile.Hash.hash alg
    (* msg *) (Seq.slice (B.as_seq h image.image_base) 0 (v image.image_size))
