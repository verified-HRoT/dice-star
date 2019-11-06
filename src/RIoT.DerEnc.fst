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
type builderContext = {
     ctxLen : uint_32;
     ctxBuf : B.lbuffer uint_8 (v ctxLen);
     ctxPos : B.pointer uint_32
}

let bufList_of_ctx
  (ctx: builderContext)
: GTot (list B.buf_t)
= [ B.buf ctx.ctxBuf
  ; B.buf ctx.ctxPos]

let locList_of_ctx
  (ctx: builderContext)
: GTot (list B.loc)
= [ B.loc_buffer ctx.ctxBuf
  ; B.loc_buffer ctx.ctxPos]

let well_formed_ctx
  (h: HS.mem)
  (ctx: builderContext)
: Type0
=
    B.all_live h (bufList_of_ctx ctx)
  /\ B.all_disjoint (locList_of_ctx ctx)
  /\ B.get h ctx.ctxPos 0 < ctx.ctxLen


//unfold let derBuilderContext = ctx: builderContext {well_formed_ctx ctx}

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
/// REF: #define CHECK_SPACE(_X)      if((_X->Length-_X->Position)<32)        {goto Error;}
open FStar.Error
let riotResult = optResult int_32 int_32

let check_space
  (_X: builderContext)
: HST.Stack bool
  (requires fun h ->
      well_formed_ctx h _X)
  (ensures  fun h0 _ h1 -> True)
=
  (_X.ctxLen - !*_X.ctxPos) < 32ul

/// REF: #define CHECK_SPACE2(_X, _N) if(((_X->Length-_X->Position)+(_N))<32) {goto Error;}
let check_space2
  (_X: builderContext)
  (_N: uint_32)
: HST.Stack bool
  (requires fun h ->
      well_formed_ctx h _X
    /\ ok I.op_Subtraction 32ul _N)
  (ensures  fun h0 _ h1 -> True)
=
  (_X.ctxLen - !*_X.ctxPos) < 32ul - _N

/// <><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>

///
/// REF: static int
///      EncodeInt(
///          uint8_t     *Buffer,
///          int          Val
///      )
let encodeInt
  (b: B.buffer uint_8)
  (value: uint_32) // <-- NOTE: Workaround
: HST.Stack riotResult
  (requires fun h ->
      B.live h b
    /\ ( (value < 128ul /\
         B.length b > 1)
      \/ (128ul <= value /\
         value < 256ul /\
         B.length b > 2)
      \/ (256ul <= value /\
         value < 166536ul /\
         B.length b > 3)))
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
      ( b.(0ul) <- cast (value % 0x100ul)
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
      ; b.(1ul) <- cast ((value / 0x100ul) % 0x100ul)
      ; b.(2ul) <- cast (value % 0x100ul)
      ; Correct 0l )
  else
///
/// REF: Error:
///          return -1;
    Error (-1l)

let g (a b: uint_32)
: Pure unit
  (requires
      ok op_Subtraction a b
    /\ a - b > 32ul)
  (ensures fun _ -> True)
=
  assert (ok (+) b 1ul)

let another_demo (x: B.pointer uint_32)
: HST.Stack unit
  (requires fun h ->
      B.live h x
    /\ ok (+) (B.get h x 0) 1ul)
  (ensures fun _ _ _ -> True)
=
  assert (ok (+) !*x 1ul);
  let a: uint_32 = !*x + 1ul in
  x *= !*x;

/// Error Message: (Error) (*?u425*) _ is not equal to the expected type y: int_t (Unsigned (W32)) {UInt.size (UInt32.v x + UInt32.v y) 32}
  //x *= !*x + 1ul; //  <- failed!
  //x.(0ul) <- x.(0ul) + 1ul; // <-- also failed
    ()


let f (a b:B.pointer uint_32)
: HST.Stack unit
  (requires fun h ->
    B.live h a /\ B.live h b /\ B.disjoint a b
    ///\ ok op_Subtraction (B.get h a 0) (B.get h b 0)
    ///\ (B.get h a 0) > (B.get h b 0)
    /\ ok (+) (B.get h b 0) 1ul
    )
  (ensures fun _ _ _ -> True)
=
  HST.push_frame();
  (a *= ((!*b) + 1ul));
  //a.(0ul) <- (b.(0ul) + 1ul);
  //assert (ok (+) b.(0ul) 1ul);
  HST.pop_frame()

///
///      int
///      DERAddUTF8String(
///          DERBuilderContext   *Context,
///          const char          *Str
///      )
let derAddUTF8String
  (ctx: builderContext)
  (#strSize: int)
  (str: C.String.t)
: HST.Stack riotResult
  (requires fun h ->
      well_formed_ctx h ctx
    /\ CS.length str = strSize
    /\ strSize <= 32
    /\ ctx.ctxLen - (B.get h ctx.ctxPos 0) >= 32ul)
  (ensures fun h0 _ h1 -> True)
=
///
/// REF:     uint32_t j, numChar = (uint32_t)strlen(Str);
  //let j: uint_32 = 0ul in
  let numChar: uint_32 = u strSize in
///
/// REF:     ASRT(numChar < 127);
  if numChar < 127ul then
///
/// REF:     CHECK_SPACE2(Context, numChar);
    if check_space2 ctx numChar then
      Error (-1l)
    else
///
/// REF:     Context->Buffer[Context->Position++] = 0x0c;
      ( ctx.ctxPos *= !*ctx.ctxPos + 1ul
      ; ctx.ctxBuf.(!*ctx.ctxPos) <- 0x0cuy

///
/// REF:     Context->Buffer[Context->Position++] = (uint8_t)numChar;
      ; ctx.ctxBuf.(ctx.ctxPos + 1ul) <- cast (numChar % 0x100ul)

      ; Correct 0l)
///          Context->Buffer[Context->Position++] = (uint8_t)numChar;
///
///          for (j = 0; j < numChar; j++) {
///              Context->Buffer[Context->Position++] = Str[j];
///          }

/// REF: Error:
///          return -1;
  else
    Error (-1l)


///
///          Context->Buffer[Context->Position++] = 0x0c;
///          Context->Buffer[Context->Position++] = (uint8_t)numChar;
///
///          for (j = 0; j < numChar; j++) {
///              Context->Buffer[Context->Position++] = Str[j];
///          }
///          return 0;
///      }
