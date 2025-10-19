let explode (s : string) : char list =
  List.init (String.length s) (String.get s)

let implode (chars : char list) : string = String.of_seq (List.to_seq chars)
let string_of_char (c : char) : string = String.make 1 c

(* Renvoie la liste l sans ses i premiers éléments. Lève l’exception
 * Failure "tropcourt" si la liste est trop courte et Failure "indiceneg"
 * lorsque i est négatif. Cette fonction est récursive terminale. *)
let rec list_skip (l : 'a list) (i : int) : 'a list =
  if i < 0 then failwith "indiceneg"
  else if i = 0 then l
  else match l with [] -> failwith "tropcourt" | x :: q -> list_skip q (i - 1)

(* Renvoie les i premiers éléments de la liste l. Lève l’exception
 * Failure "tropcourt" si la liste est trop courte et Failure "indiceneg"
 * lorsque i est négatif. *)
let rec list_beginning (l : 'a list) (i : int) : 'a list =
  if i < 0 then failwith "indiceneg"
  else if i = 0 then []
  else
    match l with
    | [] -> failwith "tropcourt"
    | x :: q -> x :: list_beginning q (i - 1)

(* Dépile n éléments de la pile s et les renvoie dans une liste. Le i-ième
 * élément de la liste est le i-ième à avoir été dépilé. Si jamais on
 * ne peut pas dépiler, lève l’erreur Stack.Empty *)
let pop_n (s : 'a Stack.t) (n : int) : 'a list =
  List.init n (fun _ -> Stack.pop s)

let rec seq_find (f : 'a -> bool) (s : 'a Seq.t) : 'a option =
  match s () with
  | Seq.Nil -> None
  | Seq.Cons (e, t) -> if f e then Some e else seq_find f t

module Hashset = struct
  type 'a t = { mutable data : ('a, unit) Hashtbl.t; mutable rw : bool }

  let create () : 'a t = { data = Hashtbl.create 8; rw = true }
  let mem (t : 'a t) a = Hashtbl.find_opt t.data a <> None

  let add (t : 'a t) a =
    if not t.rw then (
      t.data <- Hashtbl.copy t.data;
      t.rw <- true);

    Hashtbl.replace t.data a ()

  let mem_add (t : 'a t) a =
    let added = not (mem t a) in
    if added then add t a;
    added

  let remove (t : 'a t) a =
    if not t.rw then (
      t.data <- Hashtbl.copy t.data;
      t.rw <- true);
    Hashtbl.remove t.data a

  let length (t : 'a t) = Hashtbl.length t.data
  let iter f (t : 'a t) = Hashtbl.iter (fun a _ -> f a) t.data
  let is_empty (t : 'a t) = length t = 0

  let remove_one (t : 'a t) =
    match (Hashtbl.to_seq_keys t.data) () with
    | Nil -> raise (Invalid_argument "Cannot remove from an empty set")
    | Cons (key, _) ->
        remove t key;
        key

  let union (t1 : 'a t) (t2 : 'a t) =
    let res = { data = Hashtbl.create (length t1 + length t2); rw = true } in
    iter (add res) t1;
    iter (add res) t2;
    res

  let singleton (e : 'a) =
    let res = create () in
    add res e;
    res

  let intersection (t1 : 'a t) (t2 : 'a t) =
    let res = create () in
    iter (fun e -> if mem t2 e then add res e) t1;
    res

  let to_list (t : 'a t) =
    let res = ref [] in
    iter (fun e -> res := e :: !res) t;
    !res

  let of_list (l : 'a list) =
    let res = create () in
    List.iter (add res) l;
    res

  let equals (t1 : 'a t) (t2 : 'a t) =
    length t1 = length t2 && length (intersection t1 t2) = length t1

  let copy (t : 'a t) =
    t.rw <- false;
    { data = t.data; rw = false }
end

let hashtbl_remove_one (t : ('k, 'v) Hashtbl.t) =
  match (Hashtbl.to_seq_keys t) () with
  | Nil -> raise (Invalid_argument "Cannot remove from an empty set")
  | Cons (key, _) ->
      let value = Hashtbl.find t key in
      Hashtbl.remove t key;
      (key, value)
