module RIoT.Stubs

open Common

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
