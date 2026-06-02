let somme_rt l a =
  let c = ref true in
  let res = ref None in
  let l' = ref l in
  let a' = ref a in
  while !c do
    match !l' with
    | [] ->
      begin
        c := false;
        res := Some a'
      end
    | x::q ->
      begin
        l' := q;
        a' := !a'+x
      end
  done;
  Option.get !res
