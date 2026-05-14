let rec somme l a =
  match l with
  | [] -> a
  | x::q ->
      somme q (a+x)
