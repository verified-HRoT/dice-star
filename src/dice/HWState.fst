module HWState

module G = FStar.Ghost

#set-options "--__temp_no_proj HWState"

let t = bool & bool

let t_rel = fun s1 s2 ->
  Seq.length s1 == Seq.length s2 /\
  (Seq.length s1 > 0 ==>
    (let t1 = G.reveal (Seq.index s1 0) in
     let t2 = G.reveal (Seq.index s2 0) in
     match t1, t2 with
     | (true, _), (false, _)
     | (false, _), (false, true) -> True
     | _ -> if t1 = t2 then True else False))
