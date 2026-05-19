let somme_liste (l: int list) =
  let resultat = ref 0 in
  let l' = ref l in
  while !l' <> [] do
    resultat := !resultat + List.hd !l';
    l' := List.tl !l'
  done;
  !resultat
