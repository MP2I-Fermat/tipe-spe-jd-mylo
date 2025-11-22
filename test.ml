let rec sum (l : int list) = match l with [] -> 0 | x :: q -> x + sum q;;

print_endline (string_of_int (sum [ 1; 2; 3 ]))

type int_tree = Leaf of int | Node of int_tree * int * int_tree

let rec sum_tree (t : int_tree) =
  match t with
  | Leaf v -> v
  | Node (left, v, right) -> sum_tree left + v + sum_tree right
;;

print_endline (string_of_int (sum_tree (Node (Leaf 1, 2, Leaf 3))))
