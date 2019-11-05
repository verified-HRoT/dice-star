module RIoT.DerEnc

open Common
//open RIoT.Common

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

///      //
///      // Context structure for the DER-encoder. This structure contains a fixed-
///      // length array for nested SEQUENCES (which imposes a nesting limit).
///      // The buffer use for encoded data is caller-allocted.
///      //
///      typedef struct
///      {
///          uint8_t     *Buffer;        // Encoded data
///          uint32_t     Length;        // Size, in bytes, of Buffer
///          uint32_t     Position;      // Current buffer position
///
///          // SETS, SEQUENCES, etc. can be nested. This array contains the start of
///          // the payload for collection types and is set by  DERStartSequenceOrSet().
///          // Collections are "popped" using DEREndSequenceOrSet().
///          int CollectionStart[DER_MAX_NESTED];
///          int CollectionPos;
///      } DERBuilderContext;
noeq
type derBuilderContext = {
     derCtxLength   : uint_32;
     derCtxBuffer   : B.lbuffer HI.uint8 (v derCtxLength);
     derCtxPosition : uint_32
  }

let live_derCtx
  (h: Monotonic.HyperStack.mem)
  (ctx: derBuilderContext)
: GTot Type0
= B.live h ctx.derCtxBuffer

let disjoint_derCtx
  (ctx1 ctx2: derBuilderContext)
: GTot Type0
= B.disjoint ctx1.derCtxBuffer ctx2.derCtxBuffer

///      // We only have a small subset of potential PEM encodings
///      enum CertType {
///          CERT_TYPE = 0,
///          PUBLICKEY_TYPE,
///          ECC_PRIVATEKEY_TYPE,
///          CERT_REQ_TYPE,
///          LAST_CERT_TYPE
///      };
type certType =
| CERT_TYPE
| PUBLICKEY_TYPE
| ECC_PRIVATEKEY_TYPE
| CERT_REQ_TYPE
| LAST_CERT_TYPE


///
///      //
///      // This file contains basic DER-encoding routines that are sufficient to create
///      // RIoT X.509 certificates. A few corners are cut (and noted) in the interests
///      // of small code footprint and simplicity.
///      //
///      // Routines in this file encode the following types:
///      //    SEQUENCE
///      //    SET
///      //    INTEGER
///      //    OID
///      //    BOOL
///      //    PrintableString
///      //    UTF8String
///      //    UTCTime
///      //
///


///      // Assert-less assert
///      #define ASRT(_X) if(!(_X)) {goto Error;}
/// NOTE: I'm going to encode this into an if-then-else statement


///      // The encoding routines need to check that the encoded data will fit in the
///      // buffer. The following macros do (conservative) checks because it's hard to
///      // properly test low-buffer situations. CHECK_SPACE is appropriate for short
///      // additions. CHECK_SPACE2 when larger objects are being added (and the length
///      // is known.)
///      #define CHECK_SPACE(_X)      if((_X->Length-_X->Position)<32)        {goto Error;}
open FStar.Error
let riotResult = optResult int_32 int_32

let check_space
  (_X: derBuilderContext)
: HST.Stack bool
  (requires fun h ->
      live_derCtx h _X
    /\ ok I.op_Subtraction _X.derCtxLength _X.derCtxPosition)
  (ensures  fun h0 _ h1 -> True)
=
  (_X.derCtxLength - _X.derCtxPosition) < 32ul

let r: uint_8 = cast (-1l)

/// NOTE: demostrate my current encoding way
/// REF: static int
///      EncodeInt(
///          uint8_t     *Buffer,
///          int          Val
///      )
let encodeInt
  (b: B.buffer uint_8)
  (value: uint_32)
: HST.Stack riotResult
  (requires fun h ->
      B.live h b
    /\ (value < 128ul ->
          B.length b > 1
        /\ cast_ok (Unsigned W8) value)
    /\ ((128ul <= value /\ value < 256ul) ->
          B.length b > 2
        /\ cast_ok (Unsigned W8) value)
    /\ ((256ul <= value /\ value < 166536ul) ->
          B.length b > 3
        // /\ ok (/) value 256ul
        /\ within_bounds (Unsigned W32) ((v value) / 256)
        // /\ ok (%) value 256ul
        /\ within_bounds (Unsigned W32) ((v value) % 256)
        /\ cast_ok (Unsigned W8) value))
  (ensures fun h0 _ h1 -> True)
///      // DER-encode Val into buffer. Function assumes the caller knows how many
///      // bytes it will need (e.g., from GetIntEncodedNumBytes).
=
///
/// REF:     ASRT(Val < 166536);  //Recall: #define ASRT(_X) if(!(_X)) {goto Error;}
  if value < 166536ul then
///
/// REF:     if (Val <128) {
///              Buffer[0] = (uint8_t)Val;
///              return 0;
///          }
    if value < 128ul then
      ( b.(0ul) <- cast value
      ; Correct 0l )
///
/// REF:     if (Val < 256) {
///              Buffer[0] = 0x81;
///              Buffer[1] = (uint8_t)Val;
///              return 0;
///          }
    else if value < 256ul then
      ( b.(0ul) <- 0x82uy
      ; b.(1ul) <- cast value
      ; Correct 0l )
///
/// REF:     Buffer[0] = 0x82;
///          Buffer[1] = (uint8_t)(Val / 256);
///          Buffer[2] = Val % 256;
///          return 0;
    else
      ( b.(0ul) <- 0x82uy
      ; b.(1ul) <- cast (value / 256ul)
      ; b.(2ul) <- cast (value % 256ul)
      ; Correct 0l )
  else
///
/// REF: Error:
///          return -1;
    Error (-1l)
