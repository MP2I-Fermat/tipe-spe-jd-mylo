let hello_world () = print_endline "Hello, World!";;

hello_world ()

let x = 0
let rec sum (l : int list) = match l with [] -> 0 | x :: q -> x + sum q

let sum_tr (l : int list) =
  let rec sum_aux (l : int list) (s : int) =
    match l with [] -> s | x :: q -> sum_aux q (x + s)
  in
  sum_aux l 0

let _ =
  let l = [ 0; 1; 2; 3; 4; 5 ] in
  print_endline (string_of_int (sum l));
  print_endline (string_of_int (sum_tr l))
