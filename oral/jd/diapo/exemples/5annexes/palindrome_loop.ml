let palindrome_rectified_whilified (l : 'a list) (cont : 'a list -> 'ret)
    : 'ret =
  let res_ref = ref None in
  let cont_ref = ref cont in
  let l_ref = ref l in
  while !res_ref = None do
    let cont = !cont_ref in
    let l = !l_ref in
    match l with
    | [] -> res_ref := Some (cont [])
    | x :: q ->
        let new_cont (a_6 : 'a list) : 'ret = cont (a_6 @ [ x ]) in
        l_ref := q;
        cont_ref := new_cont
  done;
  Option.get !res_ref

let palindrome (l : 'a list) : 'a list =
  palindrome_rectified_whilified l (fun res -> res)
