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


let fizzbuzz max = fizzbuzz_a_partir max 1

let rec fibo_jusqua (n: int) (i: int) (last: int) (lastlast: int) =
  if n <= 1 then
    1
  else if i = n then
    last+lastlast
  else
    fibo_jusqua n (i+1) (lastlast) (last+lastlast)

let fibo n = fibo_jusqua n 2 1 1
