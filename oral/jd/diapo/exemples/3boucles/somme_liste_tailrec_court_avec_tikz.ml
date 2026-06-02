let rec somme_rt l a =
  #\tikzmark{fleche}#
  match l with
  | [] -> a
  | x::q ->
      somme_rt q (a+x)
