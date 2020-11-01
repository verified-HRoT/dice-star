module DICE.Engine.Test

open LowStar.Buffer
open FStar.HyperStack.ST

open HWAbstraction

let main ()
  : Stack C.exit_code
      (requires fun h -> uds_is_enabled h)
      (ensures fun _ _ _ -> True)
= let s = HWAbstraction.st () in
  recall_st_liveness s;
  let h0 = get () in
  push_frame ();
  let h1 = get () in
  frame_ghost_state loc_none h0 h1;
  let ret = DICE.Core.dice_main () in
  pop_frame ();
  C.EXIT_SUCCESS
