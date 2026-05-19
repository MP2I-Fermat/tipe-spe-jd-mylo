let somme l =
  let continuer = ref true in
  let res = ref 0 in
  let l' = ref l in
  while !continuer do
    match !l' with
    | [] -> continuer := false
    | x::q ->
      begin
        res := !res + x;
        l' := q
      end
  done;
  !res
