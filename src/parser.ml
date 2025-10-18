open Lexer
open Automaton
open Utils

type ('token_type, 'non_terminal) grammar_entry =
  | NonTerminal of 'non_terminal
  | Terminal of 'token_type

type ('token_type, 'non_terminal) non_terminal_or_token =
  | NonTerminalRepr of 'non_terminal
  | Token of 'token_type token

type ('token_type, 'non_terminal) derivation =
  ('token_type, 'non_terminal) grammar_entry list

type ('token_type, 'non_terminal) rule =
  'non_terminal * ('token_type, 'non_terminal) derivation

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
  ( ('token_type, 'non_terminal) grammar_entry,
    ('token_type, 'non_terminal) lr1_automaton_state )
  automaton

type ('token_type, 'non_terminal) lr1_transition =
  ('token_type, 'non_terminal) lr1_automaton_state
  * ('token_type, 'non_terminal) grammar_entry
  * ('token_type, 'non_terminal) lr1_automaton_state

(* Type « inclusion », représentant le fait que premier(d) soit inclus dans
 * chacun des premier(di) (couple (d, [d1, d2, ...]) *)
type ('token_type, 'non_terminal) inclusion =
  ('token_type, 'non_terminal) derivation (* d *)
  * ('token_type, 'non_terminal) derivation list (* [d1, d2, ...] *)

(* Renvoie l’ensemble Premier_LL(1)(s) dans la grammaire g *)
let premier_LL1 (s : ('token_type, 'non_terminal) derivation)
    (g : ('token_type, 'non_terminal) grammar) : 'token_type list =
  (* Construit une liste de paires (d, [d1, d2, ...]) telles que premier(d) soit
   * inclus dans premier(di).
   * L'ensemble des inclusions renvoyées est l’entièreté des inclusions
   * nécessaires pour construire l'ensemble premier(s) (cf. 4.2.1.3, théorème
   * 32). *)
  let rec construire_inclusions
      (derivations_a_traiter : ('token_type, 'non_terminal) derivation list)
      (inclusions : ('token_type, 'non_terminal) inclusion list) :
      ('token_type, 'non_terminal) inclusion list =
    match derivations_a_traiter with
    | [] -> inclusions
    | derivation :: derivations_a_traiter ->
        let inclus_dans_derivation =
          match derivation with
          (* premier(a) avec a terminal est prédéterminé *)
          | [ Terminal a ] -> []
          (* premier(a1) est inclus dans premier(a1...an) *)
          | x :: _ :: _ -> [ [ x ] ]
          (* Pour tout N -> a1...an, premier(a1...an) est inclus dans premier(N)
           *)
          | [ NonTerminal n ] ->
              List.filter_map (fun (n', d) -> if n = n' then Some d else None) g
          | [] -> failwith "Cannot compute premier_LL1 of an empty derivation"
        in

        (* Ajoute les inclusions spécifiées par nouveaux_inclus (pour tout d
         * dans remaining, premier(d) est inclus dans premier(derivation)) à
         * inclusions.
         * Renvoie la nouvelle liste d'inclusions et une liste de dérivations
         * jusqu'ici inconnues qui sont alors à traiter. *)
        let rec merge_inclusions
            (nouveaux_inclus : ('token_type, 'non_terminal) derivation list)
            (inclusions : ('token_type, 'non_terminal) inclusion list)
            (nouvelles_derivations :
              ('token_type, 'non_terminal) derivation list) :
            ('token_type, 'non_terminal) inclusion list
            * ('token_type, 'non_terminal) derivation list =
          (* Ajoute nouvelle_inclusion à inclusions_globales.
           * Renvoie la nouvelle valeur de inclusions_globales et un booléen
           * indiquant si nouvelle_inclusion est une dérivation jusqu'ici
           * inconnue. *)
          let rec merge_inclusion
              (nouvelle_inclusion : ('token_type, 'non_terminal) derivation)
              (inclusions_globales :
                ('token_type, 'non_terminal) inclusion list)
              (res_inclusions_globales :
                ('token_type, 'non_terminal) inclusion list) :
              ('token_type, 'non_terminal) inclusion list * bool =
            match inclusions_globales with
            | [] ->
                ( (nouvelle_inclusion, [ derivation ]) :: res_inclusions_globales,
                  not (List.mem derivation derivations_a_traiter) )
            | (d', inclusions) :: q ->
                if d' <> nouvelle_inclusion then
                  merge_inclusion nouvelle_inclusion q
                    ((d', inclusions) :: res_inclusions_globales)
                else if List.mem nouvelle_inclusion inclusions then
                  ( List.rev_append inclusions_globales res_inclusions_globales,
                    false )
                else
                  ( List.rev_append q
                      ((d', nouvelle_inclusion :: inclusions)
                      :: res_inclusions_globales),
                    false )
          in

          match nouveaux_inclus with
          | [] -> (inclusions, nouvelles_derivations)
          | x :: q ->
              let inclusions, est_inconnu = merge_inclusion x inclusions [] in
              let nouvelles_derivations =
                if est_inconnu then x :: nouvelles_derivations
                else nouvelles_derivations
              in
              merge_inclusions q inclusions nouvelles_derivations
        in

        let inclusions, nouvelles_inclusions =
          merge_inclusions inclus_dans_derivation inclusions []
        in
        construire_inclusions
          (List.rev_append nouvelles_inclusions derivations_a_traiter)
          inclusions
  in

  let inclusions = construire_inclusions [ s ] [ (s, []) ] in
  (* Une liste de paires (d, val) ou val est la valeur actuelle de premier(d).
   *)
  let valeurs = ref (List.map (fun (d, _) -> (d, [])) inclusions) in

  (* Met à jour la valeur de premier(d). *)
  let remplace_valeur (d : ('token_type, 'non_terminal) derivation)
      (valeur : 'token_type list) : unit =
    let rec remplace_valeur_dans
        (rem :
          (('token_type, 'non_terminal) derivation * 'token_type list) list)
        (res :
          (('token_type, 'non_terminal) derivation * 'token_type list) list) :
        (('token_type, 'non_terminal) derivation * 'token_type list) list =
      match rem with
      | [] -> failwith "No matching pair found"
      | ((d', _) as x) :: q ->
          if d = d' then List.rev_append q ((d, valeur) :: res)
          else remplace_valeur_dans q (x :: res)
    in
    valeurs := remplace_valeur_dans !valeurs []
  in

  let a_traiter = ref [] in

  (* Initialisation: premier(a) pour a terminal. *)
  List.iter
    (fun (d, _) ->
      match d with
      | [ Terminal a ] ->
          ignore (remplace_valeur d [ a ]);
          a_traiter := d :: !a_traiter
      | _ -> ())
    inclusions;

  (* Saturation. *)
  while !a_traiter <> [] do
    let derivation = List.hd !a_traiter in
    a_traiter := List.tl !a_traiter;
    let valeur_derivation = List.assoc derivation !valeurs in
    let derivation_inclus_dans = List.assoc derivation inclusions in
    List.iter
      (fun d ->
        let valeur_d = List.assoc d !valeurs in
        let nouvelle_valeur_d =
          List.rev_append valeur_derivation valeur_d |> List.sort_uniq compare
        in
        remplace_valeur d nouvelle_valeur_d;
        if valeur_d <> nouvelle_valeur_d then
          if not (List.mem d !a_traiter) then a_traiter := d :: !a_traiter)
      derivation_inclus_dans
  done;

  List.assoc s !valeurs

(* Renvoie l’ensemble Premier_LR(1)(s, σ) dans la grammaire g *)
let premier_LR1 (s : ('token_type, 'non_terminal) derivation)
    (sigma : 'token_type list) (g : ('token_type, 'non_terminal) grammar) :
    'token_type list =
  match s with [] -> sigma | _ -> premier_LL1 s g

(* Renvoie une copie de la liste l où les deux premiers éléments de chaque
 * triplet sont uniques dans la liste et les c' de chaque triplet (a, b, c')
 * sont la réunion sans doublons de tous les c tels que (a, b, c) est dans l
 * Exemple : cf. tests *)
let regroupe_union (l : ('a * 'b * 'c list) list) : ('a * 'b * 'c list) list =
  (* S’il n’existe pas de (a, b, _) dans l, ajoute (a, b, c) à l. Sinon, en
   * supposant qu’il existe un unique (a, b, c') dans l, renvoie l où c' est
   * remplacée par c@c' *)
  let rec ajoute_union (l : ('a * 'b * 'c list) list)
      ((a, b, c) : 'a * 'b * 'c list) : ('a * 'b * 'c list) list =
    match l with
    | [] -> [ (a, b, c) ]
    | (x, x', c') :: q when (x, x') = (a, b) -> (a, b, c @ c') :: q
    | (x, x', c') :: q -> (x, x', c') :: ajoute_union q (a, b, c)
  in
  (* Comme regroupe_union mais en partant de l' (i.e. fait un ajoute_union à l'
   * sur chaque élément de l) *)
  let rec renverse_union (l : ('a * 'b * 'c list) list)
      (l' : ('a * 'b * 'c list) list) : ('a * 'b * 'c list) list =
    match l with [] -> l' | x :: q -> renverse_union q (ajoute_union l' x)
  in
  renverse_union l []
  |> List.map (fun (a, b, c) -> (a, b, List.sort_uniq compare c))

(* Renvoie la fermeture de e un ensemble de situations LR(1). Le calcul se fait
 * par saturation. Il n’y a pas plusieurs fois la même situation mais avec deux
 * σ différents. *)
let fermeture_situations_LR1
    (e : ('token_type, 'non_terminal) lr1_situation list)
    (g : ('token_type, 'non_terminal) grammar) :
    ('token_type, 'non_terminal) lr1_situation list =
  (* Si le non-terminal de regle est nt, renvoie la situation nt->^γ~σ2.
   * Renvoie None sinon *)
  let nouvelle_situation_regle (nt : 'non_terminal) (sigma2 : 'token_type list)
      (regle : ('token_type, 'non_terminal) rule) :
      ('token_type, 'non_terminal) lr1_situation option =
    if fst regle = nt then Some (regle, 0, sigma2) else None
  in
  (* Sachant une situation s: N -> α^Tβ~σ avec T un non-terminal, renvoie
   * la liste des situations T->^γ~premierLR1(β, σ) pour T->γ règle de g *)
  let liste_nouvelles_situations
      (s : ('token_type, 'non_terminal) lr1_situation) :
      ('token_type, 'non_terminal) lr1_situation list option =
    let regle, indice, sigma = s in
    let regle_fin = list_skip (snd regle) indice in
    match regle_fin with
    | [] -> None
    | NonTerminal nt :: beta ->
        let premier = premier_LR1 beta sigma g in
        Some (List.filter_map (nouvelle_situation_regle nt premier) g)
    | _ -> None
  in
  (* Fait une étape supplémentaire de la saturation, à partir de f un ensemble
   * intermédiaire entre e et la fermeture. *)
  let etape_saturation (f : ('token_type, 'non_terminal) lr1_situation list) :
      ('token_type, 'non_terminal) lr1_situation list =
    f :: List.filter_map liste_nouvelles_situations f
    |> List.concat |> List.sort_uniq compare
  in
  (* Effectue la saturation en s’arrêtant dès qu’on atteint la stabilité *)
  let rec saturation (f : ('token_type, 'non_terminal) lr1_situation list) :
      ('token_type, 'non_terminal) lr1_situation list =
    let f' = etape_saturation f in
    if f = f' then f else saturation f'
  in
  regroupe_union (saturation e)

(* Renvoie la fermeture des situations LR(1) de la situation (regle, 0, [eof])
 * si le non-terminal de la règle est l’axiome, None sinon. *)
let transforme_axiome_en_situations (g : ('token_type, 'non_terminal) grammar)
    (axiome : 'non_terminal) (lexeme_eof : 'token_type)
    (regle : ('token_type, 'non_terminal) rule) :
    ('token_type, 'non_terminal) lr1_situation list option =
  if fst regle = axiome then
    Some (fermeture_situations_LR1 [ (regle, 0, [ lexeme_eof ]) ] g)
  else None

(* Construit l’automate LR(1) de la grammaire g. eof_token désigne le lexème
 * de fin de fichier, il ne doit pas être utilisé dans les règles de la
 * grammaire (mais il devra figurer dans la sortie de l’analyseur lexical) *)
let construit_automate_LR1 (g : ('token_type, 'non_terminal) grammar)
    (axiome : 'non_terminal) (lexeme_eof : 'token_type) :
    ('token_type, 'non_terminal) lr1_automaton =
  (* Étant donné une liste l de situations LR(1), renvoie la liste des terminaux
   * et non terminaux pouvant être lus, concaténée (sans doublons) avec
   * accu supposée sans doublons. Cette fonction est récursive terminale. *)
  let rec liste_terminaux_et_non_terminaux_a_iterer
      (l : ('token_type, 'non_terminal) lr1_situation list)
      (accu : ('token_type, 'non_terminal) grammar_entry list) :
      ('token_type, 'non_terminal) grammar_entry list =
    match l with
    | [] -> accu
    | ((_, rule), idx, _) :: q ->
        if idx = List.length rule then
          liste_terminaux_et_non_terminaux_a_iterer q accu
        else
          let alpha = List.nth rule idx in
          let nouvel_accu = alpha :: accu |> List.sort_uniq compare in
          liste_terminaux_et_non_terminaux_a_iterer q nouvel_accu
  in
  (* Renvoie la liste des situations LR(1) parmi l dont le symbole sous le
   * curseur est alpha *)
  let alpha_sous_le_curseur
      (l : ('token_type, 'non_terminal) lr1_situation list)
      (alpha : ('token_type, 'non_terminal) grammar_entry) :
      ('token_type, 'non_terminal) lr1_situation list =
    List.filter
      (fun ((_, rule), idx, _) ->
        if idx = List.length rule then false else List.nth rule idx = alpha)
      l
  in
  (* À partir d’une liste tnt de terminaux et de non terminaux à itérer,
   * construit, pour chaque alpha de tnt, la transition partant de l’état e
   * (liste de situations LR(1)) étiquetée par alpha, puis renvoie la liste
   * de ces transitions concaténée avec accu_transitions.
   * Renvoie également la liste des états atteints par ces transitions, en
   * concaténant avec accu_etats. *)
  let rec nouvelles_transitions
      (tnt : ('token_type, 'non_terminal) grammar_entry list)
      (e : ('token_type, 'non_terminal) lr1_situation list)
      (accu_transitions : ('token_type, 'non_terminal) lr1_transition list)
      (accu_etats : ('token_type, 'non_terminal) lr1_automaton_state list) :
      ('token_type, 'non_terminal) lr1_transition list
      * ('token_type, 'non_terminal) lr1_automaton_state list =
    match tnt with
    | [] -> (accu_transitions, accu_etats)
    | alpha :: q ->
        let liste_a_fermer =
          alpha_sous_le_curseur e alpha
          |> List.map (fun (r, idx, s) -> (r, idx + 1, s))
        in
        let e' = fermeture_situations_LR1 liste_a_fermer g in
        let t = (e, alpha, e') in
        let nouvel_accu_e = e' :: accu_etats in
        let nouvel_accu_t = t :: accu_transitions in
        nouvelles_transitions q e nouvel_accu_t nouvel_accu_e
  in
  (* Ajoute à l’automate toutes les transitions (et éventuellement les états)
   * depuis chaque état de a_traiter, en ajoutant les états qu’il faut traiter
   * à a_traiter. deja_vu est la liste (triée sans doublons) d’états déjà vus.
   *)
  let rec construit_automate
      (automate : ('token_type, 'non_terminal) lr1_automaton)
      (a_traiter : ('token_type, 'non_terminal) lr1_automaton_state list)
      (deja_vu : ('token_type, 'non_terminal) lr1_automaton_state list) :
      ('token_type, 'non_terminal) lr1_automaton =
    match a_traiter with
    | [] -> automate
    | e :: q ->
        (* e est une liste de situations LR(1) *)
        if List.mem e deja_vu then construit_automate automate q deja_vu
        else
          let tnt = liste_terminaux_et_non_terminaux_a_iterer e [] in
          let transitions, etats = nouvelles_transitions tnt e [] [] in
          let nouveaux_etats =
            List.sort_uniq compare (etats @ automate.states)
          in
          let nouvelles_transitions =
            List.sort_uniq compare (transitions @ automate.transitions)
          in
          let nouvel_automate =
            {
              states = nouveaux_etats;
              initial_states = automate.initial_states;
              final_states = automate.final_states;
              transitions = nouvelles_transitions;
            }
          in
          let nouveaux_deja_vus = List.sort_uniq compare (e :: deja_vu) in
          construit_automate nouvel_automate
            (List.rev_append etats a_traiter)
            nouveaux_deja_vus
  in
  let etat_initial =
    List.filter_map (transforme_axiome_en_situations g axiome lexeme_eof) g
    |> List.concat |> regroupe_union
  in
  construit_automate
    {
      states = [ etat_initial ];
      initial_states = [ etat_initial ];
      final_states = [];
      transitions = [];
    }
    [ etat_initial ] []

(* Renvoie None si `a` est sans conflits LR(1), et un état de `a` présentant un
 * conflit sinon. *)
let trouve_conflits (a : ('token_type, 'non_terminal) lr1_automaton) :
    ('token_type, 'non_terminal) lr1_automaton_state option =
  (* Renvoie true ssi `s` est un état LR(1) présentant un conflit. *)
  let est_conflit (s : ('token_type, 'non_terminal) lr1_automaton_state) : bool
      =
    (* Renvoie l'union des ensembles suivants pour toutes les situations à
     * réduction si aucun conflit réduire/réduire n'est trouvé.
     * Sinon, renvoie None. *)
    let rec suivants_situations_finales
        (situations : ('token_type, 'non_terminal) lr1_situation list)
        (res : 'token_type list) : 'token_type list option =
      match situations with
      | [] -> Some res
      | ((_, derivation), curseur, suivant) :: q ->
          if curseur <> List.length derivation then
            (* Cet état n'est pas un candidat pour la réduction *)
            suivants_situations_finales q res
          else if
            List.for_all
              (fun token_type -> not (List.mem token_type res))
              suivant
          then suivants_situations_finales q (List.rev_append suivant res)
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
            (((_, derivation), curseur, _) :
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
        List.exists (fun situation -> est_conflit_lire_reduire situation) s
  in

  let rec trouve_conflit
      (remaining_states : ('token_type, 'non_terminal) lr1_automaton_state list)
      : ('token_type, 'non_terminal) lr1_automaton_state option =
    match remaining_states with
    | [] -> None
    | s :: q -> if est_conflit s then Some s else trouve_conflit q
  in

  trouve_conflit a.states

(* Renvoie true si la situation s est une situation à réduction, false sinon *)
let a_reduire (s : ('token_type, 'non_terminal) lr1_situation) : bool =
  let (_, rule), idx, _ = s in
  idx = List.length rule

(* À partir d’un état e et d’un terminal t, renvoie une règle que l’on peut
 * réduire (i.e. une situation N->a_1…a_n^ ~ σ où t∈σ) ou None s’il n’y en
 * n’a pas. *)
let rec trouve_reduction_a_faire
    (e : ('token_type, 'non_terminal) lr1_automaton_state) (t : 'token_type) :
    ('token_type, 'non_terminal) rule option =
  match e with
  | [] -> None
  | (rule, idx, sigma) :: q ->
      if a_reduire (rule, idx, sigma) && List.mem t sigma then Some rule
      else trouve_reduction_a_faire q t

let parse (a : ('token_type, 'non_terminal) lr1_automaton)
    (eof_symbol: 'token_type)
    (texte : 'token_type token list)
    (axiome : 'non_terminal) :
    ('token_type, 'non_terminal) syntax_tree =
  if trouve_conflits a <> None then failwith ("L'automate présente des conflits" ^
    " - la grammaire n'est pas LR(1)");
  let pile_arbres: ('token_type, 'non_terminal) syntax_tree Stack.t =
    Stack.create () in
  let pile_etats = Stack.create () in

  let etat_initial = match a.initial_states with
  | [x] -> x
  | _ -> failwith ("L’automate n’est pas déterministe (plusieurs ou aucun " ^
                   "état(s) initial(aux)")
  in
  Stack.push etat_initial pile_etats;
  let etat_courant = ref etat_initial in

  let nouveau_texte = List.map (fun x -> Token x) texte in

  let rec parse_a_partir
      (text: ('token_type, 'non_terminal) non_terminal_or_token list) :
      ('token_type, 'non_terminal) syntax_tree =
    match text with
    | [] -> begin
        match Stack.pop_opt pile_arbres with
        | None -> failwith "Aucun arbre n’a été généré !";
        | Some sommet -> begin
          if not (Stack.is_empty pile_arbres) then
            failwith ("La lecture du texte a été terminée avant la fin de " ^
                      "l’analyse syntaxique");
          match sommet with
          | Leaf _ ->
              failwith "L’arbre généré n’est pas issu de l’axiome"
          | Node (s, _) when s <> axiome ->
              failwith "L’arbre généré n’est pas issu de l’axiome"
          | Node (s, e) -> Node (s, e)
          end
        end
    | x::q ->
      match x with
      | NonTerminalRepr nt ->
          let nouvelles_liste_etats = List.filter_map
            (fun (e1, t, e2) ->
              if (e1, t) = (!etat_courant, NonTerminal nt) then
                Some e2
              else
                None)
            a.transitions in
          etat_courant := begin match nouvelles_liste_etats with
            | [e] -> e
            | _ -> failwith "Impossible de lire !"
          end;
          Stack.push !etat_courant pile_etats;
          parse_a_partir q
      | Token t -> begin
        match trouve_reduction_a_faire !etat_courant t.token_type with
        | None ->
            let debut_transition = (!etat_courant, Terminal t.token_type) in
            let nouvelles_liste_etats = List.filter_map
              (fun (e1, tnt, e2) ->
                if (e1, tnt) = debut_transition then Some e2 else None)
              a.transitions in
            etat_courant := begin match nouvelles_liste_etats with
              | [e] -> e
              | _ -> failwith "Impossible de lire !"
            end;
            Stack.push !etat_courant pile_etats;
            (* La ligne suivante ne figure pas dans l’algo du livre *)
            Stack.push (Leaf t) pile_arbres;
            parse_a_partir q
        | Some (nt, regle) ->
            let n = List.length regle in
            let n_arbres = pop_n pile_arbres n |> List.rev in
            Stack.push (Node (nt, n_arbres)) pile_arbres;
            let _ = pop_n pile_etats n in
            etat_courant := Stack.top pile_etats;
            if t.token_type = eof_symbol then
              parse_a_partir [NonTerminalRepr nt]
            else
              parse_a_partir (NonTerminalRepr nt::text)
      end
  in
  parse_a_partir nouveau_texte

(*************************** Fonctions d’affichage ***************************)
let string_of_symbol (s : (char, char) grammar_entry) : string =
  match s with Terminal c | NonTerminal c -> string_of_char c

let string_of_situation (((n, rule), idx, sigma) : (char, char) lr1_situation) :
    string =
  let ns = string_of_char n in
  let rule_chars =
    List.map (fun x -> match x with Terminal c | NonTerminal c -> c) rule
  in
  let rule_beginning = implode (list_beginning rule_chars idx) in
  let rule_end = implode (list_skip rule_chars idx) in
  let sigma_s = List.map string_of_char sigma |> String.concat ", " in
  ns ^ " -> " ^ rule_beginning ^ "^" ^ rule_end ^ " ~ {" ^ sigma_s ^ "}"

let string_of_state (s : (char, char) lr1_automaton_state) : string =
  let strings = List.map string_of_situation s in
  "(" ^ String.concat ", " strings ^ ")"

let print_lr1_automaton (a : (char, char) lr1_automaton) : unit =
  print_automaton string_of_symbol string_of_state a

let print_syntax_tree (t : ('token_type, 'non_terminal) syntax_tree)
    (string_of_non_terminal : 'non_terminal -> string)
    (string_of_token : 'token_type token -> string) =
  let rec print_syntax_tree_indent (indent : string)
      (t : ('token_type, 'non_terminal) syntax_tree) =
    match t with
    | Leaf token -> print_endline (indent ^ string_of_token token)
    | Node (nt, children) ->
        print_endline (indent ^ string_of_non_terminal nt ^ ":");
        List.iter
          (fun child -> print_syntax_tree_indent (indent ^ "  ") child)
          children
  in
  print_syntax_tree_indent "" t
(*****************************************************************************)
