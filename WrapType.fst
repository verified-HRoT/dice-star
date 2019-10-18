module WrapType

open FStar.Integers
open FStar.HyperStack.ST
open LowStar.BufferOps
module B = LowStar.Buffer

let _CDI_LENGTH : uint_32 = 0x20ul

noeq
type cdi_t (len: uint_32) =
| CDI : v: B.lbuffer uint_8 (v len) -> cdi_t  len

let use_cdi
  (#len: uint_32)
  (cdi: cdi_t len)
: St unit
=
  let cdi_value : B.lbuffer uint_8 (v len) = CDI?.v cdi in
  ()

let main ()
: St unit
=
  push_frame();
  let cdi : cdi_t _CDI_LENGTH
    = CDI (B.alloca 0x00uy _CDI_LENGTH) in
  use_cdi cdi;
  pop_frame();
  ()
