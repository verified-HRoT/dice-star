module Minimal.Main

open Minimal.DICE
open Minimal.RIoT

module HST = FStar.HyperStack.ST

let main ()
: HST.St C.exit_code
=
  riotStart
    Minimal.DICE._DICE_DIGEST_LENGTH  // <-- length of CDI
    (diceStart ());                   // <-- compute CDI

  C.EXIT_SUCCESS
