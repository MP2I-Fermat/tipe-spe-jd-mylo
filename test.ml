let rec sum (l : int list) : int = match l with [] -> 0 | x :: q -> x + sum q
;;

print_endline (string_of_int (sum [ 1; 2; 3 ]))

type int_tree = Leaf of int | Node of int_tree * int * int_tree

let rec sum_tree (t : int_tree) : int =
  match t with
  | Leaf v -> v
  | Node (left, v, right) -> sum_tree left + v + sum_tree right
;;

print_endline (string_of_int (sum_tree (Node (Leaf 1, 2, Leaf 3))))

let rec fibonacci (n : int) : int =
  if n = 0 || n = 1 then 1 else fibonacci (n - 1) + fibonacci (n - 2)
;;

print_endline (string_of_int (fibonacci 10))

let rec custom_fold_left (fn : 'acc -> 'el -> 'ac) (init : 'acc) (l : 'el list)
    : 'ac =
  match l with [] -> init | x :: q -> custom_fold_left fn (fn init x) q

let rec sum_even_numbers (l : int list) : int =
  match l with
  | [] -> 0
  | x :: q -> if x mod 2 = 0 then x + sum_even_numbers q else sum_even_numbers q

let rec is_even_length (l : 'a list) : bool =
  match l with [] -> true | _ :: q -> not (is_even_length q)

let rec length (l : 'a list) : int =
  match l with [] -> 0 | _ :: q -> 1 + length q

let rec f () : unit =
  let rec g () : unit = f () in
  g ()

type 'a tree = Leaf of 'a | Node of 'a tree list

let rec visit_children f children =
  match children with
  | [] -> ()
  | x :: q ->
      visit_tree f x;
      visit_children f q

and visit_tree f tree =
  match tree with
  | Leaf label -> f label
  | Node children -> visit_children f children

let rec visit_tree2 (f : 'a -> unit) (t : 'a tree) : unit =
  let rec iter_list (g : 'b -> unit) (l : 'b list) : unit =
    match l with
    | [] -> ()
    | x :: q ->
        g x;
        iter_list g q
  in
  match t with
  | Leaf l -> f l
  | Node children -> iter_list (fun child -> visit_tree2 f child) children
