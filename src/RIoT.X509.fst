module RIoT.X509

open Common

open LowStar.BufferOps
open FStar.Integers
//open Lib.IntTypes

open Spec.Hash.Definitions
open Hacl.Hash.Definitions

module I  = FStar.Integers
module HI  = Lib.IntTypes

module SHA2= Hacl.Hash.SHA2
module HMAC= Hacl.HMAC
module Ed25519 = Hacl.Ed25519

module CL  = C.Loops
module CE  = C.Endianness
module CF  = C.Failure
module C   = C
module CS  = C.String
module S   = FStar.Seq
module IB  = LowStar.ImmutableBuffer
module B   = LowStar.Buffer
module M   = LowStar.Modifies
module HS  = FStar.HyperStack
module HST = FStar.HyperStack.ST

let _BIGLEN : I.uint_32 = 0x09ul

noeq
type bigval_t = {
     data : B.lbuffer HI.uint32 (v _BIGLEN)
  }

/// REF:
/// typedef struct {
///     bigval_t x;
///     bigval_t y;
///     uint32_t infinity;
/// } affine_point_t;
noeq
type affine_point_t = {
     x: bigval_t;
     y: bigval_t;
     infinity: B.pointer HI.uint32
  }
type riot_ecc_publickey = affine_point_t


let live_affine_point
  (h: HS.mem)
  (p: affine_point_t)
: Type0
=   B.live h p.x.data
  /\ B.live h p.y.data
  /\ B.live h p.infinity
let live_ecc_publickey = live_affine_point

/// REF:
/// typedef struct {
///     bigval_t r;
///     bigval_t s;
/// } ECDSA_sig_t;
noeq
type ecdsa_sig_t = {
     r: bigval_t;
     s: bigval_t
  }
type riot_ecc_privatekey = ecdsa_sig_t

let live_ecdsa_sig
  (h: HS.mem)
  (s: ecdsa_sig_t)
: Type0
=   B.live h s.r.data
  /\ B.live h s.s.data
type live_ecc_privatekey = live_ecdsa_sig

assume val unit32_to_bigendian
  (i: I.uint_32)
: I.uint_32

/// TODO
#reset-options "--z3rlimit 50 --max_fuel 50 --max_ifuel 50"
let riot_KDF_FIXED
  (#fixed_size: I.uint_32{(v fixed_size) > 0})
  (fixed: B.lbuffer HI.uint8 (v fixed_size))
  (#label_size: I.uint_32{(v label_size) > 0})
  (label: B.lbuffer HI.uint8 (v label_size))
  (#context_size: I.uint_32{(v context_size) > 0})
  (context: B.lbuffer HI.uint8 (v context_size))
  (numberOfBits: I.uint_32)
  (total_size: B.pointer I.uint_32)
: HST.Stack unit
  (requires fun h ->
      B.live h fixed
    /\ B.live h label
    /\ B.live h context
    /\ B.live h total_size
    /\ B.disjoint fixed label
    /\ B.disjoint fixed context
    /\ B.disjoint context label
    /\ B.disjoint total_size fixed
    /\ B.disjoint total_size label
    /\ B.disjoint total_size context
    /\ I.ok (+) label_size context_size
    /\ I.ok (+) (label_size + context_size) 5ul
/// REF: assert(fixedSize >= total);
    /\ fixed_size >= (label_size + context_size + 5ul))
  (ensures  fun h0 _ h1 -> True)
=
  HST.push_frame();

/// REF: size_t  total = (((label) ? labelSize : 0) + ((context) ? contextSize : 0) + 5);
  total_size.(0ul) <- label_size + context_size + 5ul;

/// REF: if (label) {
///        memcpy(fixed, label, labelSize);
///        fixed += labelSize;
///    }
  //memcpy fixed label label_size;
  //let fixed' = B.sub fixed 0ul label_size in

/// REF: *fixed++ = 0;
  //fixed'.(1ul) <- (HI.u8 0x00);

/// REF: if (context) {
///        memcpy(fixed, context, contextSize);
///        fixed += contextSize;
///      }
  //memcpy fixed' context context_size;
  //let fixed'' = B.sub fixed 0ul label_size in

/// REF: numberOfBits = UINT32_TO_BIGENDIAN(numberOfBits);
  let numberOfBits = unit32_to_bigendian numberOfBits in
/// REF: memcpy(fixed, &numberOfBits, 4);
  //memcpy fixed''
/// REF: return total;

  HST.pop_frame()

type hashMagic_t = I.uint_64
let _SHA256_BLOCK_LENGTH = block_len SHA2_256
let _SHA256_DIGEST_LENGTH = hash_len SHA2_256
let _HMAC_SHA256_BLOCK_LENGTH = block_len SHA2_256
let _HMAC_SHA256_DIGEST_LENGTH = hash_len SHA2_256

noeq
type riot_SHA256_CONTEXT = {
     state: B.lbuffer HI.uint8 8;
     magic_: hashMagic_t;
     bitcount: I.uint_64;
     buffer: B.lbuffer HI.uint8 (v _SHA256_BLOCK_LENGTH)
  }

noeq
type riot_HMAC_SHA256_CTX = {
     hashCtx: riot_SHA256_CONTEXT;
     opad: B.lbuffer HI.uint8 (v _HMAC_SHA256_BLOCK_LENGTH);
  }

#reset-options "--z3rlimit 50 --max_fuel 50 --max_ifuel 50"
#push-options "--query_stats"
let test
  (a:I.uint_32)
  (b:I.uint_32)
  (c:B.pointer I.uint_32)
: HST.Stack unit
  (requires fun h ->
      B.live h c
    /\ I.ok (+) 1ul (B.get h c 0))
  (ensures  fun h0 _ h1 -> True)
=
  let c : I.uint_32 = 1ul + !*c in
  ()

assume val riot_HMAC_SHA256_Init
  (ctx: riot_HMAC_SHA256_CTX)
  (#keyLen: I.uint_32{v keyLen > 0})
  (key: B.lbuffer HI.uint8 (v keyLen))
: HST.Stack unit
  (requires fun h -> True)
  (ensures  fun h0 _ h1 -> True)

assume val riot_HMAC_SHA256_Update
  (ctx: riot_HMAC_SHA256_CTX)
  (#dataLen: I.uint_32{v dataLen > 0})
  (data: B.lbuffer HI.uint8 (v dataLen))
: HST.Stack unit
  (requires fun h -> True)
  (ensures  fun h0 _ h1 -> True)

assume val riot_HMAC_SHA256_Final
  (ctx: riot_HMAC_SHA256_CTX)
  (#digestLen: I.uint_32{v digestLen > 0})
  (digest: B.lbuffer HI.uint8 (v digestLen))
: HST.Stack unit
  (requires fun h -> True)
  (ensures  fun h0 _ h1 -> True)

let riot_KDF_SHA256
  (#out_size: I.uint_32{v out_size > 0})
  (out: B.lbuffer HI.uint8 (v out_size))
  (#key_size: I.uint_32{v key_size > 0})
  (key: B.lbuffer HI.uint8 (v key_size))
  (#fixed_size: I.uint_32{v fixed_size > 0})
  (fixed: B.lbuffer HI.uint8 (v fixed_size))
  (counter: B.pointer HI.uint32)
: HST.Stack unit
  (requires fun h ->
      B.live h counter
    /\ B.live h out
    /\ B.live h key
    /\ B.disjoint counter out
    /\ B.disjoint counter key
    /\ B.disjoint key out
    /\ I.ok (+) (B.get h counter 0) (HI.U32 1))
  (ensures  fun h0 _ h1 -> True)
=
  HST.push_frame();

/// REF: RIOT_HMAC_SHA256_CTX    ctx;
  let ctx: riot_HMAC_SHA256_CTX = {
      hashCtx = {
        state = B.alloca (HI.u8 0x00) 8ul;
        magic_ = 0uL;
        bitcount = 0uL;
        buffer = B.alloca (HI.u8 0x00) _SHA256_BLOCK_LENGTH
      };
      opad = B.alloca (HI.u8 0x00) _HMAC_SHA256_BLOCK_LENGTH
  } in

/// NOTE: Why `(!*counter) + 1ul` won't pass the type check?
/// REF: uint32_t                ctr = counter ? ++*counter : 1;
  let ctr: B.pointer HI.uint32
    = B.alloca ((HI.u32 1) + !*counter) 1ul in

  riot_HMAC_SHA256_Init
    ctx
    key;

  riot_HMAC_SHA256_Update
    ctx
    ctr;

  riot_HMAC_SHA256_Update
    ctx
    fixed;

  riot_HMAC_SHA256_Final
    ctx
    out;

  HST.pop_frame()


let ecdh_derive
  (p1: affine_point_t)
  (k: bigval_t)
  (src: bigval_t)
  (label_size: I.uint_32)
  (label: B.lbuffer HI.uint8 (I.v label_size))
: HST.Stack unit
  (requires fun h ->
      live_affine_point h p1
    /\ B.live h k.data)
  (ensures  fun h0 _ h1 -> True)
=
  HST.push_frame();

  k.data.(_BIGLEN - 1ul) <- (HI.u32 0);

  HST.pop_frame()
