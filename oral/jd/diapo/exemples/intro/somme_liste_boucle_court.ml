let somme l =
  let c = ref true in
  let res = ref 0 in
  let l' = ref l in
  while !c do
    match !l' with
    | [] -> c := false
    | x::q ->
      begin
        res := !res + x;
        l' := q
      end
  done;
  !res
