(* Commentaire *)

let fizzbuzz (max: int) =
  let rec fizzbuzz_a_partir (n: int) =
    if n > max then
      ()
    else
      if n mod 15 = 0 then
        print_endline "fizzbuzz"
      else if n mod 5 = 0 then
        print_endline "buzz"
      else if n mod 3 = 0 then
        print_endline "fizz"
      else
        (print_int n; print_newline ())
      ;
      fizzbuzz_a_partir (n+1)
  in
  fizzbuzz_a_partir 0

