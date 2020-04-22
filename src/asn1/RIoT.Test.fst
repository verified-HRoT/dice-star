module RIoT.Test

open LowParse.Low.Base
open LowParse.Low.Combinators

open ASN1.Spec
open ASN1.Low

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module MB = LowStar.Monotonic.Buffer
module B = LowStar.Buffer
module Cast = FStar.Int.Cast
module C = C

open FStar.Integers

let main ()
: HST.St C.exit_code
= C.EXIT_SUCCESS

