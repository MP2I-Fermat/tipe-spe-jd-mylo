(* Commentaire *)

let rec fizzbuzz_a_partir (max: int) (n: int) : unit =
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


let fizzbuzz (max: int) : unit = fizzbuzz_a_partir max 1

let rec fibo_jusqua (n: int) (i: int) (last: int) (lastlast: int) =
  if n <= 1 then
    1
  else if i = n then
    last+lastlast
  else
    fibo_jusqua n (i+1) (lastlast) (last+lastlast)

let fibo n = fibo_jusqua n 2 1 1

let rec map (f: 'a -> 'b) (l: 'a list) : 'b list =
  match l with
  | [] -> []
  | x::q -> (f x)::(map f q)


let rec sum (l : int list) : int =
  match l with
  | [] -> 0
  | x :: q -> x + sum q


type 'a abr =
    Feuille of 'a
  | Noeud of 'a * 'a abr * 'a abr


let rec recherche_abr (abr: 'a abr) (valeur: 'a) : bool =
  match abr with
  | Feuille a -> a = valeur
  | Noeud(t, g, d) ->
      begin
      if valeur <= t then
        recherche_abr g valeur
      else
        recherche_abr d valeur
      end

let rec insert_abr (abr: 'a abr) (valeur: 'a) : 'a abr =
  match abr with
  | Feuille a ->
      begin
      if valeur < a then Noeud(valeur, Feuille(valeur), Feuille(a))
      else if valeur > a then Noeud(a, Feuille(a), Feuille(valeur))
      else Feuille a
      end
  | Noeud(t, g, d) ->
      begin
      if valeur <= t then
        Noeud(t, insert_abr g valeur, d)
      else
        Noeud(t, g, insert_abr d valeur)
      end
