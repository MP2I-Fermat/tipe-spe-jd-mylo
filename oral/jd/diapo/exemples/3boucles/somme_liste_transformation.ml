let rec somme l a =
  let c = ref true in
  let res = ref None in
  let l' = l in
  let a' = a in
  match #\tikzmark{startarg}#l#\tikzmark{stoparg}# with
  | [] -> #\tikzmark{startreturn}#a#\tikzmark{stopreturn}#
  | x::q ->
      #\tikzmark{startcall}#somme q (a+x)#\tikzmark{stopcall}#
