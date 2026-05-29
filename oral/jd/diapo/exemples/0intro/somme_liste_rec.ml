let rec somme_liste (l: int list) : int =
  match l with
  | [] -> 0
  | x::q -> x + somme_liste q
