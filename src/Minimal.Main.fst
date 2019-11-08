module Minimal.Main

open Minimal.DICE
open Minimal.RIoT

module HST = FStar.HyperStack.ST

let main ()
: HST.Stack C.exit_code
  (requires fun _ -> True)
  (ensures  fun _ _ _ -> True)
=
  riotStart
    Minimal.DICE._DICE_DIGEST_LENGTH
    (diceStart ());

  C.EXIT_SUCCESS
