let rec somme l a =
  #\tikzmark{fleche}#
  match l with
  | [] -> a
  | x::q ->
      somme q (a+x)
