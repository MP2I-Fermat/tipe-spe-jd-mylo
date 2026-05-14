let somme_rectified_whilified l acc =
  let res_ref = ref None in
  let acc_ref = ref acc in
  let l_ref = ref l in
  while !res_ref = None do
    let acc = !acc_ref in
    let l = !l_ref in
    match l with
    | [] -> res_ref := Some acc
    | x :: q ->
        let new_acc a_7 = x + a_7 in
        begin
          l_ref := q;
          acc_ref := new_acc acc
        end
  done;
  Option.get !res_ref

let somme l = somme_rectified_whilified l 0

let () =
  print_int (somme (List.init 50_000_000 (fun i -> i)));
  print_newline ()
