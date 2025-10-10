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

let test_premier_LL1 =
  let grammaire1 (* page 123, exemple 144 *) =
    [ ('S', [ Terminal 'a'; NonTerminal 'T' ]); ('T', [ Terminal 'b' ]) ]
  in
  assert (premier_LL1 [ Terminal 'a'; NonTerminal 'T' ] grammaire1 = [ 'a' ]);
  assert (premier_LL1 [ NonTerminal 'T' ] grammaire1 = [ 'b' ]);
  let grammaire2 (* page 60, exemple 24 *) =
    [
      ('S', [ NonTerminal 'U' ]);
      ('S', [ NonTerminal 'V' ]);
      ('U', [ Terminal 'a'; Terminal 'b' ]);
      ('V', [ Terminal 'c'; Terminal 'd' ]);
    ]
  in
  assert (premier_LL1 [ Terminal 'a'; Terminal 'b' ] grammaire2 = [ 'a' ]);
  assert (premier_LL1 [ Terminal 'c'; Terminal 'd' ] grammaire2 = [ 'c' ]);
  assert (premier_LL1 [ NonTerminal 'U' ] grammaire2 = [ 'a' ]);
  assert (premier_LL1 [ NonTerminal 'V' ] grammaire2 = [ 'c' ]);
  assert (premier_LL1 [ NonTerminal 'S' ] grammaire2 = [ 'a'; 'c' ])


(* Renvoie l’ensemble Premier_LR(1)(s, σ) dans la grammaire g *)
let premier_LR1 (s : ('token_type, 'non_terminal) grammar_entry list)
    (sigma: 'token_type list)
    (g : ('token_type, 'non_terminal) grammar) : 'token_type list =
      match s with
      | [] -> sigma
      | _ -> premier_LL1 s g


(* Renvoie la fermeture de e un ensemble de situations LR(1). Le calcul se fait
 * par saturation *)
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
  saturation e


let test_fermeture_situations_LR1 : unit =
  (* Dans les examples suivants, les symboles « drapeau » dans le livre sont
   * représentés par le caractère 'e' (pour “end of file”) *)
  (* page 123, example 148 *)
  let regle1 = ('S', [Terminal 'a'; NonTerminal 'T'; Terminal 'c']) in
  let regle2 = ('T', [Terminal 'b']) in
  let g = [regle1; regle2] in
  let situation1 = (regle1, 0, ['e']) in
  let situation2 = (regle1, 1, ['e']) in
  let situation3 = (regle2, 0, ['c']) in
  assert (fermeture_situations_LR1 [situation1] g = [situation1]);
  assert (fermeture_situations_LR1 [situation2] g = [situation2; situation3]);
  (* page 124, example 149 *)
  let regle1 =
    ('S', [Terminal 'a'; NonTerminal 'T'; NonTerminal 'U']) in
  let regle2 = ('T', [Terminal 'b']) in
  let regle3 = ('U', [Terminal 'c']) in
  let g = [regle1; regle2; regle3] in
  let situation1 = (regle1, 0, ['e']) in
  let situation2 = (regle1, 1, ['e']) in
  let situation3 = (regle2, 0, ['c']) in
  assert (fermeture_situations_LR1 [situation1] g = [situation1]);
  assert (fermeture_situations_LR1 [situation2] g = [situation2; situation3]);
  (* Ensemble vide *)
  assert (fermeture_situations_LR1 [] [] = [])


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
      let nouveaux_deja_vus = List.sort_uniq compare e::deja_vu in
      construit_automate
        nouvel_automate
        (List.rev_append nouveaux_etats a_traiter)
        nouveaux_deja_vus
  in
  let etat_initial =
    List.filter_map (transforme_axiome_en_situations g axiome lexeme_eof) g
    |> List.concat
    |> List.sort_uniq compare
  in
  construit_automate {
    states = [etat_initial];
    initial_states = [etat_initial];
    final_states = [];
    transitions = []
  } [etat_initial] []


let test_construit_automate_LR1 : unit =
  let regle1 = ('S', [Terminal 'i']) in
  let regle2 =
    ('S', [Terminal 'i'; Terminal '['; Terminal 'c'; Terminal ']'])
  in
  let g = [regle1; regle2] in
  let eof = 'e' in
  let situation11 = (regle1, 0, [eof]) in
  let situation12 = (regle2, 0, [eof]) in
  let situation21 = (regle1, 1, [eof]) in
  let situation22 = (regle2, 1, [eof]) in
  let situation3 = (regle2, 2, [eof]) in
  let situation4 = (regle2, 3, [eof]) in
  let situation5 = (regle2, 4, [eof]) in
  let etat1 = [situation11; situation12] in
  let etat2 = [situation21; situation22] in
  let etat3 = [situation3] in
  let etat4 = [situation4] in
  let etat5 = [situation5] in
  let etats = List.sort compare [etat1; etat2; etat3; etat4; etat5] in
  let transitions = List.sort compare [
    (etat1, Terminal 'i', etat2);
    (etat2, Terminal '[', etat3);
    (etat3, Terminal 'c', etat4);
    (etat4, Terminal ']', etat5);
  ] in
  let a = {
    states = etats;
    initial_states = [etat1];
    final_states = [];
    transitions = transitions
  } in
  assert (construit_automate_LR1 g 'S' eof = a)


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

(*
let parse (g : ('token_type, 'non_terminal) grammar)
    (text : 'token_type token list) : ('token_type, 'non_terminal) syntax_tree =
  _
*)
