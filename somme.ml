let rec somme l =
  match l with
  | [] -> 0
  | x::q -> x + somme q


let () = print_int (somme (List.init 50_000_000 (fun i -> i))); print_newline ()
