let hello_world () = print_endline "Hello, World!";;

hello_world ()

type 'a my_list = Empty | Cons of 'a * 'a my_list

let rec sum (l : int my_list) =
  match l with Empty -> 0 | Cons (a, q) -> a + sum q

let sum_tr (l : int my_list) =
  let rec sum_aux (l : int my_list) (acc : int) =
    match l with Empty -> acc | Cons (a, q) -> sum_aux q (acc + a)
  in
  sum_aux l 0

let _ =
  let l = Cons (1, Cons (2, Cons (3, Empty))) in
  print_endline (string_of_int (sum l));
  print_endline (string_of_int (sum_tr l))
