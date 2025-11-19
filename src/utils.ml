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

  let add_absent (t : 'a t) a =
    if not t.rw then (
      t.data <- Hashtbl.copy t.data;
      t.rw <- true);

    Hashtbl.add t.data a ()

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
    t1.data == t2.data
    || length t1 = length t2
       && Hashtbl.to_seq t1.data |> Seq.for_all (fun (k, ()) -> mem t2 k)

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

module BitSet = struct
  let available_bits_per_int = 31

  type t = { data : int array; mutable length : int }

  let create (n : int) : t =
    let required_ints = ((n - 1) / available_bits_per_int) + 1 in
    { data = Array.make required_ints 0; length = 0 }

  let _deconstruct (n : int) : int * int =
    (n / available_bits_per_int, n mod available_bits_per_int)

  let _reconstruct (i : int) (o : int) : int = (i * available_bits_per_int) + o

  let add (s : t) (n : int) : unit =
    let i, o = _deconstruct n in
    let prev = s.data.(i) in
    let curr = prev lor (1 lsl o) in
    s.data.(i) <- curr;
    if curr <> prev then s.length <- s.length + 1

  let add_all (s : t) (s' : t) : unit =
    for i = 0 to Array.length s.data - 1 do
      let new_value = s.data.(i) lor s'.data.(i) in
      if new_value <> s.data.(i) then (
        let added = ref (s.data.(i) lxor new_value) in
        while !added <> 0 do
          if !added land 1 <> 0 then s.length <- s.length + 1;
          added := !added lsr 1
        done;
        s.data.(i) <- new_value)
    done

  let mem (s : t) (n : int) : bool =
    let i, o = _deconstruct n in
    s.data.(i) land (1 lsl o) <> 0

  let length (s : t) : int = s.length
  let is_empty (s : t) : bool = length s = 0

  let remove (s : t) (n : int) : unit =
    let i, o = _deconstruct n in
    let prev = s.data.(i) in
    let curr = prev land lnot (1 lsl o) in
    s.data.(i) <- curr;
    if prev <> curr then s.length <- s.length - 1

  let remove_one (s : t) : int =
    let rec remove_one_from (i : int) : int =
      if s.data.(i) <> 0 then (
        let o = ref 0 in
        while s.data.(i) land (1 lsl !o) = 0 do
          incr o
        done;
        let res = _reconstruct i !o in
        remove s res;
        res)
      else remove_one_from (i + 1)
    in
    remove_one_from 0

  let iter (f : int -> unit) (s : t) : unit =
    for i = 0 to Array.length s.data - 1 do
      let base = i * available_bits_per_int in
      let value = ref s.data.(i) in
      let o = ref 0 in
      while !value <> 0 do
        if !value land 1 <> 0 then f (base + !o);
        value := !value lsr 1;
        incr o
      done
    done

  let copy (s : t) : t = { data = Array.copy s.data; length = s.length }

  let equals (s1 : t) (s2 : t) : bool =
    s1.length = s2.length && s1.data = s2.data

  let intersection (s1 : t) (s2 : t) : t =
    let res = create (Array.length s1.data * available_bits_per_int) in
    iter (fun n -> if mem s2 n then add res n) s1;
    res
end
