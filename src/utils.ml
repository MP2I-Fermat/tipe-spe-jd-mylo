let explode (s : string) : char list =
  List.init (String.length s) (String.get s)

let implode (chars : char list) : string = String.of_seq (List.to_seq chars)

let string_of_char (c: char) : string = String.make 1 c

(* Renvoie la liste l sans ses i premiers éléments. Lève l’exception
 * Failure "tropcourt" si la liste est trop courte et Failure "indiceneg"
 * lorsque i est négatif. Cette fonction est récursive terminale. *)
let rec list_skip (l: 'a list) (i: int) : 'a list =
  if i < 0 then failwith "indiceneg"
  else if i = 0 then l
  else
    match l with
    | [] -> failwith "tropcourt"
    | x::q -> list_skip q (i-1)


(* Renvoie les i premiers éléments de la liste l. Lève l’exception
 * Failure "tropcourt" si la liste est trop courte et Failure "indiceneg"
 * lorsque i est négatif. *)
let rec list_beginning (l: 'a list) (i: int) : 'a list =
  if i < 0 then failwith "indiceneg"
  else if i = 0 then []
  else
    match l with
    | [] -> failwith "tropcourt"
    | x::q -> x::(list_beginning q (i-1))

