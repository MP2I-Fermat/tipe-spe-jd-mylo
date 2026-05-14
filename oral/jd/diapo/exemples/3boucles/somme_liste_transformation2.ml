let somme l a =
  let c = ref true in
  let res = ref None in
  let l' = ref l in
  let a' = ref a in
  match #\tikzmark{startarg}#!l'#\tikzmark{stoparg}# with
  | [] ->
    begin
      #\tikzmark{startreturn}#c := false;
      res := Some a'#\tikzmark{stopreturn}#
    end
  | x::q ->
    begin
      #\tikzmark{startcall}#l' := q;
      a' := !a'+x#\tikzmark{stopcall}#
    end

