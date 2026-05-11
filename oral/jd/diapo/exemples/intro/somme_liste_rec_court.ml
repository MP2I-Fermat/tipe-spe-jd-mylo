let rec somme l =
  match l with
  | [] -> 0
  | x::q ->
      x + somme q
