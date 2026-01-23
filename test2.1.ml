(* Commentaire *)

let rec fizzbuzz_a_partir (max: int) (n: int) =
  if n > max then
    ()
  else begin
    if n mod 15 = 0 then
      print_endline "fizzbuzz"
    else if n mod 5 = 0 then
      print_endline "buzz"
    else if n mod 3 = 0 then
      print_endline "fizz"
    else
      (print_int n; print_newline ())
    ;
    fizzbuzz_a_partir max (n+1)
  end

