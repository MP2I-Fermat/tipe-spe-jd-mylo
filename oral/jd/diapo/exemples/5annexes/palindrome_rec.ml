let rec palindrome (l: 'a list) : 'a list =
  match l with
  | [] -> []
  | x::q -> (palindrome q)@[x]
