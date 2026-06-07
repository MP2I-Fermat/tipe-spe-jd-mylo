let fizzbuzz_a_partir_rectified_whilified (max : int) (n : int) (acc : unit) :
    unit =
  let res_ref = ref None in
  let acc_ref = ref acc in
  let n_ref = ref n in
  let max_ref = ref max in
  while !res_ref = None do
    let acc = !acc_ref in
    let n = !n_ref in
    let max = !max_ref in
    if n > max then res_ref := Some acc
    else (
      if n mod 15 = 0 then print_endline "fizzbuzz"
      else if n mod 5 = 0 then print_endline "buzz"
      else if n mod 3 = 0 then print_endline "fizz"
      else (
        print_int n;
        print_newline ());
      begin
        max_ref := max;
        n_ref := n + 1;
        acc_ref := acc
      end)
  done;
  Option.get !res_ref

let fizzbuzz_a_partir (max : int) (n : int) : unit =
  fizzbuzz_a_partir_rectified_whilified max n ()

let fizzbuzz (max : int) : unit = fizzbuzz_a_partir max 1

let fibo_jusqua_rectified_whilified (n : int) (i : int) (last : int)
    (lastlast : int) cont =
  let res_ref = ref None in
  let cont_ref = ref cont in
  let lastlast_ref = ref lastlast in
  let last_ref = ref last in
  let i_ref = ref i in
  let n_ref = ref n in
  while !res_ref = None do
    let cont = !cont_ref in
    let lastlast = !lastlast_ref in
    let last = !last_ref in
    let i = !i_ref in
    let n = !n_ref in
    if n <= 1 then res_ref := Some (cont 1)
    else if i = n then res_ref := Some (cont (last + lastlast))
    else begin
      n_ref := n;
      i_ref := i + 1;
      last_ref := lastlast;
      lastlast_ref := last + lastlast;
      cont_ref := cont
    end
  done;
  Option.get !res_ref

let fibo_jusqua (n : int) (i : int) (last : int) (lastlast : int) =
  fibo_jusqua_rectified_whilified n i last lastlast (fun res -> res)

let fibo n = fibo_jusqua n 2 1 1

let map_rectified_whilified (f : 'a -> 'b) (l : 'a list)
    (cont : 'b list -> 'ret) : 'ret =
  let res_ref = ref None in
  let cont_ref = ref cont in
  let l_ref = ref l in
  let f_ref = ref f in
  while !res_ref = None do
    let cont = !cont_ref in
    let l = !l_ref in
    let f = !f_ref in
    match l with
    | [] -> res_ref := Some (cont [])
    | x :: q ->
        let new_cont (a_12 : 'b list) : 'ret = cont (f x :: a_12) in
        begin
          f_ref := f;
          l_ref := q;
          cont_ref := new_cont
        end
  done;
  Option.get !res_ref

let map (f : 'a -> 'b) (l : 'a list) : 'b list =
  map_rectified_whilified f l (fun res -> res)

let sum_rectified_whilified (l : int list) (acc : int) : int =
  let res_ref = ref None in
  let acc_ref = ref acc in
  let l_ref = ref l in
  while !res_ref = None do
    let acc = !acc_ref in
    let l = !l_ref in
    match l with
    | [] -> res_ref := Some acc
    | x :: q ->
        let new_acc (a_7 : int) : int = x + a_7 in
        begin
          l_ref := q;
          acc_ref := new_acc acc
        end
  done;
  Option.get !res_ref

let sum (l : int list) : int = sum_rectified_whilified l 0

type 'a abr = Feuille of 'a | Noeud of 'a * 'a abr * 'a abr

let recherche_abr_rectified_whilified (abr : 'a abr) (valeur : 'a)
    (cont : bool -> 'ret) : 'ret =
  let res_ref = ref None in
  let cont_ref = ref cont in
  let valeur_ref = ref valeur in
  let abr_ref = ref abr in
  while !res_ref = None do
    let cont = !cont_ref in
    let valeur = !valeur_ref in
    let abr = !abr_ref in
    match abr with
    | Feuille a -> res_ref := Some (cont (a = valeur))
    | Noeud (t, g, d) ->
        if valeur <= t then begin
          abr_ref := g;
          valeur_ref := valeur;
          cont_ref := cont
        end
        else begin
          abr_ref := d;
          valeur_ref := valeur;
          cont_ref := cont
        end
  done;
  Option.get !res_ref

let recherche_abr (abr : 'a abr) (valeur : 'a) : bool =
  recherche_abr_rectified_whilified abr valeur (fun res -> res)

let insert_abr_rectified_whilified (abr : 'a abr) (valeur : 'a)
    (cont : 'a abr -> 'ret) : 'ret =
  let res_ref = ref None in
  let cont_ref = ref cont in
  let valeur_ref = ref valeur in
  let abr_ref = ref abr in
  while !res_ref = None do
    let cont = !cont_ref in
    let valeur = !valeur_ref in
    let abr = !abr_ref in
    match abr with
    | Feuille a ->
        res_ref :=
          Some
            (cont
               (if valeur < a then Noeud (valeur, Feuille valeur, Feuille a)
                else if valeur > a then Noeud (a, Feuille a, Feuille valeur)
                else Feuille a))
    | Noeud (t, g, d) ->
        if valeur <= t then
          let new_cont (a_74 : 'a abr) : 'ret = cont (Noeud (t, a_74, d)) in
          begin
            abr_ref := g;
            valeur_ref := valeur;
            cont_ref := new_cont
          end
        else
          let new_cont (a_91 : 'a abr) : 'ret = cont (Noeud (t, g, a_91)) in
          begin
            abr_ref := d;
            valeur_ref := valeur;
            cont_ref := new_cont
          end
  done;
  Option.get !res_ref

let insert_abr (abr : 'a abr) (valeur : 'a) : 'a abr =
  insert_abr_rectified_whilified abr valeur (fun res -> res)
