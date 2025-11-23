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

module TerminalSet = struct
  let available_bits_per_int = 31

  type 'a mapping = {
    direct : ('a, int) Hashtbl.t;
    reverse : 'a array;
    item_count : int;
  }

  type 'a t = { mapping : 'a mapping; mutable length : int; data : int array }

  let build_mapping (token_types : 'a list) : 'a mapping =
    let direct = Hashtbl.create 8 in
    List.iter
      (fun token_type ->
        if not (Hashtbl.mem direct token_type) then
          Hashtbl.add direct token_type (Hashtbl.length direct))
      token_types;

    let reverse =
      Array.init (Hashtbl.length direct) (fun _ -> List.hd token_types)
    in

    Hashtbl.iter (fun k v -> reverse.(v) <- k) direct;

    { direct; item_count = Hashtbl.length direct; reverse }

  let create (mapping : 'a mapping) =
    let data_length =
      int_of_float
        (ceil
           (float_of_int mapping.item_count
           /. float_of_int available_bits_per_int))
    in
    { mapping; length = 0; data = Array.make data_length 0 }

  let add (s : 'a t) (item : 'a) : unit =
    let i = Hashtbl.find s.mapping.direct item in
    let prev = s.data.(i / available_bits_per_int) in
    s.data.(i / available_bits_per_int) <-
      s.data.(i / available_bits_per_int)
      lor (1 lsl (i mod available_bits_per_int));
    if prev <> s.data.(i / available_bits_per_int) then s.length <- s.length + 1

  let length (s : 'a t) = s.length

  let iter (f : 'a -> unit) (s : 'a t) =
    for i = 0 to Array.length s.data - 1 do
      if s.data.(i) <> 0 then
        for j = 0 to available_bits_per_int - 1 do
          if s.data.(i) land (1 lsl j) <> 0 then
            f s.mapping.reverse.(j + (i * available_bits_per_int))
        done
    done

  let copy (s : 'a t) =
    { mapping = s.mapping; length = s.length; data = Array.copy s.data }

  let equals (s1 : 'a t) (s2 : 'a t) =
    if s1.length != s2.length || s1.mapping != s2.mapping then false
    else
      let equal_so_far = ref true in
      let i = ref 0 in
      while !equal_so_far && !i < Array.length s1.data do
        equal_so_far := s1.data.(!i) = s2.data.(!i);
        incr i
      done;
      !equal_so_far

  let singleton (mapping : 'a mapping) (item : 'a) : 'a t =
    let res = create mapping in
    add res item;
    res

  let is_empty (s : 'a t) = s.length = 0

  let intersection (s1 : 'a t) (s2 : 'a t) : 'a t =
    let res =
      {
        mapping = s1.mapping;
        data =
          Array.init (Array.length s1.data) (fun i ->
              s1.data.(i) land s2.data.(i));
        length = 0;
      }
    in
    iter (fun _ -> res.length <- res.length + 1) res;
    res

  let mem (s : 'a t) (item : 'a) =
    let idx = Hashtbl.find_opt s.mapping.direct item in
    match idx with
    | None -> false
    | Some idx ->
        s.data.(idx / available_bits_per_int)
        land (1 lsl (idx mod available_bits_per_int))
        <> 0

  let to_seq (s : 'a t) : 'a Seq.t =
    let res = ref (fun () -> Seq.Nil) in
    iter (fun item -> res := fun () -> Seq.Cons (item, !res)) s;
    !res
end
