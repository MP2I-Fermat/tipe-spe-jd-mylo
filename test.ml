let rec sum (l : int list) = match l with [] -> 0 | x :: q -> x + sum q;;

print_endline (string_of_int (sum [ 1; 2; 3 ]))
