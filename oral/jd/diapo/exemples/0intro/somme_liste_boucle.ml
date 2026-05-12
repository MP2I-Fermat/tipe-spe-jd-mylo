let somme_liste (l: int array) =
  let resultat = ref 0 in
  for i = 0 to Array.length l do
    resultat := !resultat + l.(i)
  done;
  !resultat
