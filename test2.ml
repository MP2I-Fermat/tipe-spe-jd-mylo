let sum (l : int list) =
  let rec sum_aux (l : int list)
      (aux_continue : 'aux_continue_type -> 'aux_continue_type) =
    aux_continue (match l with [] -> 0 | x :: q -> x + sum_aux q (fun x -> x))
  in
  sum_aux l (fun x -> x)
;;

print_endline (string_of_int (sum [ 1; 2; 3 ]))
