open Lexer
open Automaton
open Utils

type ('token_type, 'non_terminal) grammar_entry =
  | NonTerminal of 'non_terminal
  | Terminal of 'token_type

type ('token_type, 'non_terminal) rule =
  'non_terminal * ('token_type, 'non_terminal) grammar_entry list

type ('token_type, 'non_terminal) grammar =
  ('token_type, 'non_terminal) rule list

type ('token_type, 'non_terminal) syntax_tree =
  | Node of 'non_terminal * ('token_type, 'non_terminal) syntax_tree list
  | Leaf of 'token_type token

(* Représente les situations LR(1), du style
 * α₁…αⱼ↑ α₁₊ⱼ…αₙ ~ {b₁…bₙ} *)
type ('token_type, 'non_terminal) lr1_situation =
  ('token_type, 'non_terminal) rule * int * 'token_type list


type ('token_type, 'non_terminal) lr1_automaton_state =
  ('token_type, 'non_terminal) lr1_situation list

(* Représente un automate LR(1) *)
type ('token_type, 'non_terminal) lr1_automaton =
  (
    ('token_type, 'non_terminal) grammar_entry,
    ('token_type, 'non_terminal) lr1_automaton_state
  ) automaton

type ('token_type, 'non_terminal) lr1_transition =
  ('token_type, 'non_terminal) lr1_automaton_state *
  ('token_type, 'non_terminal) grammar_entry *
  ('token_type, 'non_terminal) lr1_automaton_state


(* Renvoie l’ensemble Premier_LL(1)(s) dans la grammaire g *)
let premier_LL1 (s : ('token_type, 'non_terminal) grammar_entry list)
    (g : ('token_type, 'non_terminal) grammar) : 'token_type list =
  (* Renvoie l’ensemble Premier_n_LL(1)(s) et un booléen qui indique si
   * cet Premier_i_LL(1)(s) est constant à partir du rang n (cf. preuve). Le
   * booléen n’est pas toujours à true à partir du premier rang, mais il sera
   * forcément à true au bout d’un moment. *)
  let rec premier_n (n : int)
      (s : ('token_type, 'non_terminal) grammar_entry list) :
      'token_type list * bool =
    if n = 0 then
      match s with
      | [ Terminal a ] -> ([ a ], true)
      | _ -> ([], false)
    else
      match s with
      | [ NonTerminal a1 ] ->
          let premier_nm1, premier_est_constant = premier_n (n - 1) s in
          if premier_est_constant then (premier_nm1, true)
          else
            let derivations =
              List.filter_map
                (fun (symbol, derivation) ->
                  if symbol = a1 then Some derivation else None)
                g
            in
            let premiers_et_variations_derivations =
              List.map (premier_n (n - 1)) derivations
            in
            let premiers_derivations_sont_constantes =
              List.for_all
                (fun (_, est_constant) -> est_constant)
                premiers_et_variations_derivations
            in
            let premiers_derivations =
              List.map fst premiers_et_variations_derivations
            in
            let prem_n =
              List.fold_left List.rev_append premier_nm1 premiers_derivations
              |> List.sort_uniq compare
            in
            (* (premier_i(N)) est en fait constant à partir du rang n - 1 (voir
             * preuves/premier_n_cts). On ne s'en rend compte que maintenant car
             * on n'avait pas calculé premier_n des derivations possibles. *)
            ( prem_n,
              premiers_derivations_sont_constantes && prem_n = premier_nm1 )
      | a1 :: _ ->
          let prem_nm1, prem_est_constant = premier_n (n - 1) s in
          if prem_est_constant then (prem_nm1, true)
          else
            let prem_nm1_a1, prem_a1_est_constant = premier_n (n - 1) [ a1 ] in
            let prem_n =
              List.rev_append prem_nm1_a1 prem_nm1 |> List.sort_uniq compare
            in
            (* premier_i(a1...am) est constant à partir du rang n - 1 (voir
             * preuves/premier_n_cts). *)
            (prem_n, prem_a1_est_constant && prem_n = prem_nm1)
      | [] -> failwith "Les règles N -> ε ne sont pas gérées"
  in
  let rec trouve_premier_constant (n : int) =
    let premier_n, est_constant = premier_n n s in
    if est_constant then premier_n else trouve_premier_constant (n + 1)
  in
  trouve_premier_constant 0


(* Renvoie l’ensemble Premier_LR(1)(s, σ) dans la grammaire g *)
let premier_LR1 (s : ('token_type, 'non_terminal) grammar_entry list)
    (sigma: 'token_type list)
    (g : ('token_type, 'non_terminal) grammar) : 'token_type list =
      match s with
      | [] -> sigma
      | _ -> premier_LL1 s g


(* Renvoie une copie de la liste l où les deux premiers éléments de chaque
 * triplet sont uniques dans la liste et les c' de chaque triplet (a, b, c')
 * sont la réunion sans doublons de tous les c tels que (a, b, c) est dans l
 * Exemple : cf. tests *)
let regroupe_union (l: ('a * 'b * 'c list) list) : ('a * 'b * 'c list) list =
  (* S’il n’existe pas de (a, b, _) dans l, ajoute (a, b, c) à l. Sinon, en
   * supposant qu’il existe un unique (a, b, c') dans l, renvoie l où c' est
   * remplacée par c@c' *)
  let rec ajoute_union
      (l: ('a * 'b * 'c list) list)
      ((a, b, c): ('a * 'b * 'c list))
      : ('a * 'b * 'c list) list =
    match l with
    | [] -> [(a, b, c)]
    | (x, x', c')::q when (x, x') = (a, b) -> (a, b, c@c')::q
    | (x, x', c')::q -> (x, x', c')::(ajoute_union q (a, b, c))
  in
  (* Comme regroupe_union mais en partant de l' (i.e. fait un ajoute_union à l'
   * sur chaque élément de l) *)
  let rec renverse_union (l: ('a * 'b * 'c list) list) (l': ('a * 'b * 'c list) list)
      : ('a * 'b * 'c list) list =
    match l with
    | [] -> l'
    | x::q -> renverse_union q (ajoute_union l' x)
  in
  renverse_union l [] |>
    List.map (fun (a, b, c) -> (a, b, List.sort_uniq compare c))


(* Renvoie la fermeture de e un ensemble de situations LR(1). Le calcul se fait
 * par saturation. Il n’y a pas plusieurs fois la même situation mais avec deux
 * σ différents. *)
let fermeture_situations_LR1
    (e: ('token_type, 'non_terminal) lr1_situation list)
    (g: ('token_type, 'non_terminal) grammar):
    ('token_type, 'non_terminal) lr1_situation list =
  (* Si le non-terminal de regle est nt, renvoie la situation nt->^γ~σ2.
   * Renvoie None sinon *)
  let nouvelle_situation_regle (nt: 'non_terminal)
      (sigma2: 'token_type list)
      (regle: ('token_type, 'non_terminal) rule) :
      ('token_type, 'non_terminal) lr1_situation option =
    if fst regle = nt then
      Some (regle, 0, sigma2)
    else None
  in
  (* Sachant une situation s: N -> α^Tβ~σ avec T un non-terminal, renvoie
   * la liste des situations T->^γ~premierLR1(β, σ) pour T->γ règle de g *)
  let liste_nouvelles_situations (s: ('token_type, 'non_terminal) lr1_situation) :
    ('token_type, 'non_terminal) lr1_situation list option =
      let regle, indice, sigma = s in
      let regle_fin = list_skip (snd regle) indice in
      match regle_fin with
      | [] -> None
      | (NonTerminal nt)::beta ->
          let premier = premier_LR1 beta sigma g in
          Some (List.filter_map (nouvelle_situation_regle nt premier) g)
      | _ -> None
  in
  (* Fait une étape supplémentaire de la saturation, à partir de f un ensemble
   * intermédiaire entre e et la fermeture. *)
  let etape_saturation (f: ('token_type, 'non_terminal) lr1_situation list) :
    ('token_type, 'non_terminal) lr1_situation list =
      f::(List.filter_map liste_nouvelles_situations f)
      |> List.concat
      |> List.sort_uniq compare
  in
  (* Effectue la saturation en s’arrêtant dès qu’on atteint la stabilité *)
  let rec saturation (f: ('token_type, 'non_terminal) lr1_situation list) :
      ('token_type, 'non_terminal) lr1_situation list =
    let f' = etape_saturation f in
    if f = f' then f
    else saturation f'
  in
  regroupe_union (saturation e)


(* Renvoie la fermeture des situations LR(1) de la situation (regle, 0, [eof])
 * si le non-terminal de la règle est l’axiome, None sinon. *)
let transforme_axiome_en_situations (g: ('token_type, 'non_terminal) grammar)
    (axiome: 'non_terminal) (lexeme_eof: 'token_type)
    (regle: ('token_type, 'non_terminal) rule) :
    ('token_type, 'non_terminal) lr1_situation list option =
  if fst regle = axiome then
    Some (fermeture_situations_LR1 [(regle, 0, [lexeme_eof])] g)
  else
    None


(* Construit l’automate LR(1) de la grammaire g. eof_token désigne le jeton
 * de fin de fichier, il ne doit pas être utilisé dans les règles de la
 * grammaire (mais il devra figurer dans la sortie de l’analyseur lexical) *)
let construit_automate_LR1 (g: ('token_type, 'non_terminal) grammar)
    (axiome: 'non_terminal) (lexeme_eof: 'token_type) :
    ('token_type, 'non_terminal) lr1_automaton =
  (* Étant donné une liste l de situations LR(1), renvoie la liste des terminaux
   * et non terminaux pouvant être lus, concaténée (sans doublons) avec
   * accu supposée sans doublons. Cette fonction est récursive terminale. *)
  let rec liste_terminaux_et_non_terminaux_a_iterer
      (l: ('token_type, 'non_terminal) lr1_situation list)
      (accu: ('token_type, 'non_terminal) grammar_entry list)
      : ('token_type, 'non_terminal) grammar_entry list =
    match l with
    | [] -> accu
    | ((_, rule), idx, _)::q ->
        if idx = List.length rule then
          liste_terminaux_et_non_terminaux_a_iterer q accu
        else
          let alpha = List.nth rule idx in
          let nouvel_accu = alpha::accu |> List.sort_uniq compare in
          liste_terminaux_et_non_terminaux_a_iterer q nouvel_accu
  in
  (* Renvoie la liste des situations LR(1) parmi l dont le symbole sous le
   * curseur est alpha *)
  let alpha_sous_le_curseur
      (l: ('token_type, 'non_terminal) lr1_situation list)
      (alpha: ('token_type, 'non_terminal) grammar_entry)
      : ('token_type, 'non_terminal) lr1_situation list =
    List.filter
      (fun ((_, rule), idx, _) ->
        if idx = List.length rule then false
        else List.nth rule idx = alpha)
      l
  in
  (* À partir d’une liste tnt de terminaux et de non terminaux à itérer,
   * construit, pour chaque alpha de tnt, la transition partant de l’état e
   * (liste de situations LR(1)) étiquetée par alpha, puis renvoie la liste
   * de ces transitions concaténée avec accu_transitions.
   * Renvoie également la liste des états atteints par ces transitions, en
   * concaténant avec accu_etats. *)
  let rec nouvelles_transitions
      (tnt: ('token_type, 'non_terminal) grammar_entry list)
      (e: ('token_type, 'non_terminal) lr1_situation list)
      (accu_transitions: ('token_type, 'non_terminal) lr1_transition list)
      (accu_etats: ('token_type, 'non_terminal) lr1_automaton_state list)
      : ('token_type, 'non_terminal) lr1_transition list *
        ('token_type, 'non_terminal) lr1_automaton_state list =
    match tnt with
    | [] -> accu_transitions, accu_etats
    | alpha::q ->
      let liste_a_fermer =
        alpha_sous_le_curseur e alpha |>
        List.map (fun (r, idx, s) -> (r, idx+1, s))
      in
      let e' = fermeture_situations_LR1 liste_a_fermer g in
      let t = (e, alpha, e') in
      let nouvel_accu_e = e'::accu_etats in
      let nouvel_accu_t = t::accu_transitions in
      nouvelles_transitions q e nouvel_accu_t nouvel_accu_e
  in
  (* Ajoute à l’automate toutes les transitions (et éventuellement les états)
   * depuis chaque état de a_traiter, en ajoutant les états qu’il faut traiter
   * à a_traiter. deja_vu est la liste (triée sans doublons) d’états déjà vus.
   *)
  let rec construit_automate
      (automate: ('token_type, 'non_terminal) lr1_automaton)
      (a_traiter: ('token_type, 'non_terminal) lr1_automaton_state list)
      (deja_vu: ('token_type, 'non_terminal) lr1_automaton_state list) :
      ('token_type, 'non_terminal) lr1_automaton =
    match a_traiter with
    | [] -> automate
    | e::q -> (* e est une liste de situations lr1 *)
      if List.mem e deja_vu then
        construit_automate automate q deja_vu
      else
        let tnt = liste_terminaux_et_non_terminaux_a_iterer e [] in
        let transitions, etats = nouvelles_transitions tnt e [] [] in
        let nouveaux_etats = List.sort_uniq compare (etats@automate.states) in
        let nouvelles_transitions =
          List.sort_uniq compare (transitions@automate.transitions)
        in
        let nouvel_automate = {
          states = nouveaux_etats;
          initial_states = automate.initial_states;
          final_states = automate.final_states;
          transitions = nouvelles_transitions
        } in
        let nouveaux_deja_vus = List.sort_uniq compare (e::deja_vu) in
        construit_automate
          nouvel_automate
          (List.rev_append etats a_traiter)
          nouveaux_deja_vus
  in
  let etat_initial =
    List.filter_map (transforme_axiome_en_situations g axiome lexeme_eof) g
    |> List.concat
    |> regroupe_union
  in
  construit_automate {
    states = [etat_initial];
    initial_states = [etat_initial];
    final_states = [];
    transitions = []
  } [etat_initial] []


(* Renvoie None si `a` est sans conflits LR(1), et un état de `a` présentant un
 * conflit sinon. *)
let trouve_conflits (a: ('token_type, 'non_terminal) lr1_automaton) :
    ('token_type, 'non_terminal) lr1_automaton_state option =
  (* Renvoie true ssi `s` est un état LR(1) présentant un conflit. *)
  let est_conflit (s: ('token_type, 'non_terminal) lr1_automaton_state) : bool =
    (* Renvoie l'union des ensembles suivants pour toutes les situations à
     * réduction si aucun conflit réduire/réduire n'est trouvé.
     * Sinon, renvoie None. *)
    let rec suivants_situations_finales
        (situations: ('token_type, 'non_terminal) lr1_situation list)
        (res: 'token_type list) :
        'token_type list option =
      match situations with
      | [] -> Some res
      | ((_, derivation), curseur, suivant)::q ->
          if curseur <> List.length derivation then
            (* Cet état n'est pas un candidat pour la réduction *)
            suivants_situations_finales q res
          else
            if List.for_all
                (fun token_type -> not (List.mem token_type res))
                suivant
            then
              suivants_situations_finales q (List.rev_append suivant res)
            else
              (* Conflit réduire/réduire. Inutile de verifier que les règles
               * causant ce conflit sont bien différentes car on les a
               * dédupliquées avec regroupe_union. *)
              None
    in

    let suivants = suivants_situations_finales s [] in
    match suivants with
    (* On a trouvé un conflit réduire/réduire. *)
    | None -> true
    | Some suivants ->
      let est_conflit_lire_reduire
          (((_, derivation), curseur, _):
           ('token_type, 'non_terminal) lr1_situation) : bool =
        (* Rien à lire dans cet état. *)
        if curseur = List.length derivation then false
        else
          let next = List.nth derivation curseur in
          match next with
          | NonTerminal _ -> false
          (* Vérifier que l'on n'a pas envie de lire un terminal candidat pour
           / une réduction. *)
          | Terminal t -> List.mem t suivants
      in
      (* S’il existe un conflit lire/réduire -> true *)
      List.exists (fun situation -> (est_conflit_lire_reduire situation)) s
  in

  let rec trouve_conflit
      (remaining_states: ('token_type, 'non_terminal) lr1_automaton_state list):
      ('token_type, 'non_terminal) lr1_automaton_state option =
    match remaining_states with
    | [] -> None
    | s::q -> if est_conflit s then Some s else trouve_conflit q
  in

  trouve_conflit a.states


let parse (a : ('token_type, 'non_terminal) lr1_automaton)
    (eof_symbol: 'token_type)
    (text : 'token_type token list) : ('token_type, 'non_terminal) syntax_tree =
  failwith "todo" (*
  let pile_arbres = Stack.Empty in
  let pile_etats = Stack.Empty in

  let initial_state = match a.initial_states with
  | [x] -> x
  | _ -> failwith "L’automate n’est pas déterministe (plusieurs ou aucun " ^
                  "état(s) initial(aux)"
  in
  Stack.push initial_state pile_etats;
  let i = ref 0 in
  let longueur_texte = List.length text
  while i <= longueur_texte do
*)


(*************************** Fonctions d’affichage ***************************)
let string_of_symbol (s: (char, char) grammar_entry) : string =
  match s with
  | Terminal c
  | NonTerminal c -> string_of_char c

let string_of_situation (((n, rule), idx, sigma): (char, char) lr1_situation)
    : string =
  let ns = string_of_char n in
  let rule_chars = List.map (
    fun x -> match x with | Terminal c | NonTerminal c -> c
  ) rule in
  let rule_beginning = implode (list_beginning rule_chars idx) in
  let rule_end = implode (list_skip rule_chars idx) in
  let sigma_s = List.map string_of_char sigma |> String.concat ", " in
  ns ^ " -> " ^ rule_beginning ^ "^" ^ rule_end ^ " ~ {" ^ sigma_s ^ "}"

let string_of_state (s: (char, char) lr1_automaton_state) : string =
  let strings = List.map string_of_situation s in
  "(" ^ (String.concat ", " strings) ^ ")"

let print_lr1_automaton (a: (char, char) lr1_automaton) : unit =
  print_automaton string_of_symbol string_of_state a
(*****************************************************************************)

