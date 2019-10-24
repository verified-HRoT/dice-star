module Common

open LowStar.BufferOps
open Lib.IntTypes

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

let ret_SUCCESS : int32 = i32 1
let ret_FAILURE : int32 = i32 0
let ret_ERROR   : int32 = i32 (-1)

let _DICE_UDS_LENGTH = 0x20

assume val uds : B.lbuffer uint8 _DICE_UDS_LENGTH

type imagePath =

noeq
type hinstance = {
     addr: B.pointer uint32
  }

assume val _DEFAULT_RIOT_PATH: B.buffer imagePath
assume val _DEFAULT_LOADER_PATH: B.buffer imagePath


noeq
type cdi_t = {
     alg: hash_alg;
     cdi: hash_t alg;
  }


type entryPoint =
assume val _RIOT_ENTRY: entryPoint
