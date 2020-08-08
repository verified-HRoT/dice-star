module RIoT.Helpers

open FStar.Char
open FStar.String

open LowStar.Printf
open LowStar.Comment
open LowStar.Failure

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module MB = LowStar.Monotonic.Buffer
module B = LowStar.Buffer
module C = C

open FStar.Integers

val write_out
  (filename: string)
  (content: B.buffer uint_8)
  (len: uint_32)
: HST.Stack unit
  (requires fun h ->
    B.live h content /\
    B.length content >= v len)
  (ensures fun h0 _ h1 ->
    B.live h1 content /\
    B.modifies B.loc_none h0 h1)

