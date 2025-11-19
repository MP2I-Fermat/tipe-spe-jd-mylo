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
  ('non_terminal, ('token_type, 'non_terminal) derivation list) Hashtbl.t

type ('token_type, 'non_terminal) syntax_tree =
  | Node of 'non_terminal * ('token_type, 'non_terminal) syntax_tree list
  | Leaf of 'token_type token

type anonymized_derivation = int array

type anonymized_grammar = {
  rules : anonymized_derivation list array;
  non_terminal_count : int;
  terminal_count : int;
  symbol_count : int;
}

(* Représente les situations LR(0), du style α₁…αⱼ↑ α₁₊ⱼ…αₙ *)
type anonymized_lr0_situation = int * int array * int

(* Représente les situations LR(1), du style α₁…αⱼ↑ α₁₊ⱼ…αₙ ~ {b₁…bₙ} *)
type anonymized_lr1_situation = anonymized_lr0_situation * BitSet.t

(* Dictionnaire de situations LR(0) a leurs ensembles premiers correspondants.
   On assure de cette façon l’unicité de la situation pour une règle donnee
   dans les états des automates LR(1). *)
type lr1_automaton_state = (anonymized_lr0_situation, BitSet.t) Hashtbl.t

(* Représente un automate LR(1) *)
type lr1_automaton = (int, lr1_automaton_state) deterministic_automaton

type ('token_type, 'non_terminal) lr1_parser = {
  automaton : lr1_automaton;
  grammar : anonymized_grammar;
  terminal_mapping : ('token_type, int) Hashtbl.t;
  non_terminal_mapping : ('non_terminal, int) Hashtbl.t;
}

type ('token_type, 'non_terminal) lr1_transition =
  lr1_automaton_state
  * ('token_type, 'non_terminal) grammar_entry
  * lr1_automaton_state

let grammar_of_rule_list (l : ('token_type, 'non_terminal) rule list) :
    ('token_type, 'non_terminal) grammar =
  let res = Hashtbl.create 8 in
  List.iter
    (fun (nt, derivation) ->
      match Hashtbl.find_opt res nt with
      | Some existing_derivations ->
          Hashtbl.replace res nt (derivation :: existing_derivations)
      | None -> Hashtbl.add res nt [ derivation ])
    l;
  res

let anonymize (g : ('token_type, 'non_terminal) grammar)
    (lexeme_eof : 'token_type) :
    anonymized_grammar
    * ('token_type, int) Hashtbl.t
    * ('non_terminal, int) Hashtbl.t =
  let non_terminal_mappings = Hashtbl.create 8 in
  g
  |> Hashtbl.iter (fun non_terminal _ ->
         if not (Hashtbl.mem non_terminal_mappings non_terminal) then
           Hashtbl.replace non_terminal_mappings non_terminal
             (Hashtbl.length non_terminal_mappings));
  let non_terminal_count = Hashtbl.length non_terminal_mappings in

  let terminal_mappings = Hashtbl.create 8 in
  Hashtbl.replace terminal_mappings lexeme_eof 0;
  g
  |> Hashtbl.iter (fun _ derivations ->
         derivations
         |> List.iter (fun derivation ->
                derivation
                |> List.iter (function
                     | NonTerminal _ -> ()
                     | Terminal t ->
                         if not (Hashtbl.mem terminal_mappings t) then
                           Hashtbl.replace terminal_mappings t
                             (non_terminal_count
                             + Hashtbl.length terminal_mappings))));
  let terminal_count = Hashtbl.length terminal_mappings in

  let anonymized_rules = Array.make non_terminal_count [] in
  non_terminal_mappings
  |> Hashtbl.iter (fun non_terminal index ->
         let derivations = Hashtbl.find g non_terminal in

         let anonymize (d : ('token_type, 'non_terminal) derivation) : int array
             =
           let rule = Array.make (List.length d) (-1) in
           List.iteri
             (fun index symbol ->
               let anonymized_symbol =
                 match symbol with
                 | NonTerminal nt -> Hashtbl.find non_terminal_mappings nt
                 | Terminal t -> Hashtbl.find terminal_mappings t
               in
               rule.(index) <- anonymized_symbol)
             d;
           rule
         in

         let anonymized_derivations = List.map anonymize derivations in
         anonymized_rules.(index) <- anonymized_derivations);

  ( {
      rules = anonymized_rules;
      non_terminal_count;
      terminal_count;
      symbol_count = non_terminal_count + terminal_count;
    },
    terminal_mappings,
    non_terminal_mappings )

let est_terminal (g : anonymized_grammar) (s : int) : bool =
  s >= g.non_terminal_count

(* Renvoie un tableau t tel que t[i] est l'ensemble Premier_LL1(i) dans g *)
let premier_LL1 (g : anonymized_grammar) : BitSet.t array =
  (* Crée un tableau d tel que d[s] est l'ensemble des derivations w tels
     que premier(s) est inclus dans premier(w).
     cf. 4.2.1.3 Théorème 32 (p 63).
     s est toujours un symbole unique de la grammaire car on travaille sans règles
     N -> epsilon.
     *)
  let construire_inclusions () : BitSet.t array =
    let inclusions =
      Array.init g.symbol_count (fun _ -> BitSet.create g.symbol_count)
    in
    let a_traiter = BitSet.create g.symbol_count in
    for i = 0 to g.symbol_count - 1 do
      BitSet.add a_traiter i
    done;

    while not (BitSet.is_empty a_traiter) do
      let symbol = BitSet.remove_one a_traiter in
      (* Only process if symbol is a non_terminal *)
      if not (est_terminal g symbol) then
        g.rules.(symbol)
        |> List.iter (fun derivation ->
               let derivation_first_symbol = derivation.(0) in
               BitSet.add inclusions.(derivation_first_symbol) symbol)
    done;

    inclusions
  in

  let inclusions = construire_inclusions () in
  let a_traiter = BitSet.create g.symbol_count in
  let valeurs =
    Array.init g.symbol_count (fun symbol ->
        let init_value = BitSet.create g.symbol_count in
        (* Base case: if symbol is terminal then its premier set contains itself. *)
        if est_terminal g symbol then (
          BitSet.add init_value symbol;
          (* Also register it as pending processing. *)
          BitSet.add a_traiter symbol);
        init_value)
  in

  (* Saturation *)
  while not (BitSet.is_empty a_traiter) do
    let symbol = BitSet.remove_one a_traiter in
    let symbol_value = valeurs.(symbol) in
    let contained_in = inclusions.(symbol) in

    contained_in
    |> BitSet.iter (fun containing_symbol ->
           let containing_value = valeurs.(containing_symbol) in
           let init_length = BitSet.length containing_value in
           BitSet.iter (BitSet.add containing_value) symbol_value;

           if init_length <> BitSet.length containing_value then
             BitSet.add a_traiter containing_symbol)
  done;

  valeurs

(* Sature e jusqu'à que e soit une fermeture des situations LR(1) de e. *)
let fermer_situations_LR1 (e : lr1_automaton_state) (g : anonymized_grammar)
    (premier : BitSet.t array) : unit =
  (* Si le non-terminal de règle est nt, renvoie la situation nt->^γ~σ2.
   * Renvoie None sinon *)
  let nouvelle_situation_regle (sigma2 : BitSet.t) (nt : int)
      (derivation : anonymized_derivation) : anonymized_lr1_situation =
    ((nt, derivation, 0), BitSet.copy sigma2)
  in

  (* Sachant une situation s : N -> α^Tβ~σ avec T un non-terminal, renvoie
   * la liste des situations T->^γ~premierLR1(β, σ) pour T->γ règle de g *)
  let liste_nouvelles_situations
      ((_, derivation, curseur) : anonymized_lr0_situation) (sigma : BitSet.t) :
      anonymized_lr1_situation list =
    if curseur >= Array.length derivation then []
    else
      let symbole_curseur = derivation.(curseur) in
      if est_terminal g symbole_curseur then []
      else
        let premier =
          (* premier_LL1 = sigma si on est a la fin de la règle *)
          if curseur + 1 >= Array.length derivation then sigma
          (* premier_LL1 = premier_LL1(β) sinon *)
            else premier.(derivation.(curseur + 1))
        in
        g.rules.(symbole_curseur)
        |> List.map (nouvelle_situation_regle premier symbole_curseur)
  in

  let a_traiter = Hashset.create () in
  Hashtbl.iter (fun k _ -> Hashset.add_absent a_traiter k) e;

  while not (Hashset.is_empty a_traiter) do
    let situation = Hashset.remove_one a_traiter in
    let sigma = Hashtbl.find e situation in
    let nouvelles_situations = liste_nouvelles_situations situation sigma in
    List.iter
      (fun (nouvelle_situation, nouveau_premier) ->
        match Hashtbl.find_opt e nouvelle_situation with
        | None ->
            (* La derivation T -> ^gamma n’était pas présente dans e. *)
            Hashtbl.add e nouvelle_situation nouveau_premier;
            Hashset.add a_traiter nouvelle_situation
        | Some premier ->
            let longueur_init = BitSet.length premier in
            BitSet.add_all premier nouveau_premier;
            if longueur_init <> BitSet.length premier then
              (* On a ajouté des elements a l'ensemble sigma de T -> ^gamma *)
              Hashset.add a_traiter nouvelle_situation)
      nouvelles_situations
  done

let states_equal (a : lr1_automaton_state) (b : lr1_automaton_state) =
  a == b
  ||
  if Hashtbl.length a <> Hashtbl.length b then false
  else
    Hashtbl.to_seq a
    |> Seq.for_all (fun (k, v) ->
           match Hashtbl.find_opt b k with
           | None -> false
           | Some v' -> BitSet.equals v v')

(* Construit l’automate LR(1) de la grammaire g. eof_token désigne le lexème
 * de fin de fichier, il ne doit pas être utilisé dans les règles de la
 * grammaire (mais il devra figurer dans la sortie de l’analyseur lexical) *)
let construit_automate_LR1 (g : ('token_type, 'non_terminal) grammar)
    (axiome : 'non_terminal) (lexeme_eof : 'token_type) :
    ('token_type, 'non_terminal) lr1_parser =
  let module LR1StateMap = struct
    include Hashtbl.Make (struct
      type t = lr1_automaton_state

      let equal s1 s2 = states_equal s1 s2

      let hash (s : t) =
        Hashtbl.fold (fun k _ acc -> acc lxor Hashtbl.hash k) s 0
    end)

    let remove_one (t : 'a t) : lr1_automaton_state =
      match (to_seq_keys t) () with
      | Nil -> raise (Invalid_argument "Cannot remove from an empty set")
      | Cons (key, _) ->
          remove t key;
          key
  end in
  let g_anon, terminal_mapping, non_terminal_mapping = anonymize g lexeme_eof in
  let axiome_anon = Hashtbl.find non_terminal_mapping axiome in
  let lexeme_eof_anon = Hashtbl.find terminal_mapping lexeme_eof in

  (* Étant donné une liste l de situations LR(1), renvoie la liste des terminaux
   * et non terminaux pouvant être lus. *)
  let rec liste_terminaux_et_non_terminaux_a_iterer (s : lr1_automaton_state) :
      BitSet.t =
    let res = BitSet.create g_anon.symbol_count in
    Hashtbl.iter
      (fun (_, regle, curseur) _ ->
        if curseur <> Array.length regle then
          let alpha = regle.(curseur) in
          BitSet.add res alpha)
      s;
    res
  in

  let premier_LL1 = premier_LL1 g_anon in

  (* On ajoute toutes les règles pour l'axiome, puis on ferme l'ensemble pour
   * obtenir l’état initial. *)
  let etat_initial = Hashtbl.create 2 in

  g_anon.rules.(axiome_anon)
  |> List.iter (fun derivation ->
         let premier = BitSet.create g_anon.symbol_count in
         BitSet.add premier lexeme_eof_anon;
         Hashtbl.add etat_initial (axiome_anon, derivation, 0) premier);

  fermer_situations_LR1 etat_initial g_anon premier_LL1;

  (* transitions[state0][symbol] est l’état atteint en lisant symbol depuis
   * state0. *)
  let transitions = LR1StateMap.create 8 in
  (* Collection des états crées. *)
  let etats = Hashset.create () in

  (* Ensemble des états à traiter, sous forme d'un dictionnaires d’états à
   * unit. *)
  let a_traiter = LR1StateMap.create 2 in
  LR1StateMap.add a_traiter etat_initial ();

  let fermeture_cache = LR1StateMap.create 2 in

  while LR1StateMap.length a_traiter <> 0 do
    let etat = LR1StateMap.remove_one a_traiter in
    Hashset.add_absent etats etat;
    (* Les transitions sortants de cet état. *)
    let transitions_etat = Hashtbl.create 2 in
    LR1StateMap.add transitions etat transitions_etat;
    let tnt = liste_terminaux_et_non_terminaux_a_iterer etat in
    BitSet.iter
      (fun alpha ->
        let nouvel_etat = Hashtbl.create 2 in

        Hashtbl.iter
          (fun (nt, derivation, curseur) v ->
            if
              curseur <> Array.length derivation && derivation.(curseur) = alpha
            then
              Hashtbl.add nouvel_etat
                (nt, derivation, curseur + 1)
                (BitSet.copy v))
          etat;

        let fermeture_nouvel_etat =
          match LR1StateMap.find_opt fermeture_cache nouvel_etat with
          | Some fermeture -> fermeture
          | None ->
              let copy = Hashtbl.copy nouvel_etat in
              fermer_situations_LR1 nouvel_etat g_anon premier_LL1;
              LR1StateMap.add fermeture_cache copy nouvel_etat;
              if LR1StateMap.find_opt transitions nouvel_etat = None then
                LR1StateMap.replace a_traiter nouvel_etat ();
              nouvel_etat
        in

        Hashtbl.add transitions_etat alpha fermeture_nouvel_etat)
      tnt
  done;

  {
    automaton =
      {
        states = etats;
        initial_state = etat_initial;
        final_states = Hashset.create ();
        transition =
          (fun state0 symbol ->
            let transitions_state0 = LR1StateMap.find transitions state0 in
            Hashtbl.find_opt transitions_state0 symbol);
      };
    grammar = g_anon;
    terminal_mapping;
    non_terminal_mapping;
  }

(* Renvoie None si `a` est sans conflits LR(1), et un état de `a` présentant un
 * conflit sinon. *)
let trouve_conflits (a : ('token_type, 'non_terminal) lr1_parser) :
    lr1_automaton_state option =
  let exception Conflit in
  (* Renvoie true ssi `s` est un état LR(1) présentant un conflit. *)
  let est_conflit (s : lr1_automaton_state) : bool =
    try
      let suivants_a_reduire = BitSet.create a.grammar.symbol_count in
      (* Recherche de conflits réduire/réduire *)
      Hashtbl.iter
        (fun (nt, derivation, curseur) v ->
          if curseur = Array.length derivation then (
            if not (BitSet.is_empty (BitSet.intersection v suivants_a_reduire))
            then raise Conflit;
            BitSet.iter (BitSet.add suivants_a_reduire) v))
        s;

      (* Recherche de conflits lire/réduire *)
      Hashtbl.iter
        (fun (_, derivation, curseur) _ ->
          if curseur <> Array.length derivation then
            if est_terminal a.grammar derivation.(curseur) then
              if BitSet.mem suivants_a_reduire derivation.(curseur) then
                raise Conflit)
        s;

      false
    with Conflit -> true
  in

  let rec trouve_conflit (remaining_states : lr1_automaton_state list) :
      lr1_automaton_state option =
    match remaining_states with
    | [] -> None
    | s :: q -> if est_conflit s then Some s else trouve_conflit q
  in

  trouve_conflit (Hashset.to_list a.automaton.states)

(* À partir d’un état e et d’un terminal t, renvoie une règle que l’on peut
 * réduire (i.e. une situation N->a_1…a_n^ ~ σ où t∈σ) ou None s’il n’y en
 * n’a pas. *)
let trouve_reduction_a_faire (e : lr1_automaton_state) (t : int) :
    (int * anonymized_derivation) option =
  (* Renvoie true si la situation s est une situation à réduction, false sinon
   *)
  let a_reduire ((_, rule, idx) : anonymized_lr0_situation) : bool =
    idx = Array.length rule
  in

  let situation_a_reduire =
    Hashtbl.to_seq e
    |> seq_find (fun (lr0_situation, sigma) ->
           a_reduire lr0_situation && BitSet.mem sigma t)
  in
  match situation_a_reduire with
  | None -> None
  | Some ((nt, derivation, _), _) -> Some (nt, derivation)

let parse (a : ('token_type, 'non_terminal) lr1_parser)
    (eof_symbol : 'token_type) (texte : 'token_type token list)
    (axiome : 'non_terminal) : ('token_type, 'non_terminal) syntax_tree =
  if trouve_conflits a <> None then
    failwith "L'automate présente des conflits – la grammaire n'est pas LR(1)";

  let reverse_non_terminal_mapping =
    Hashtbl.create (Hashtbl.length a.non_terminal_mapping)
  in
  Hashtbl.iter
    (fun k v -> Hashtbl.add reverse_non_terminal_mapping v k)
    a.non_terminal_mapping;

  let pile_arbres : ('token_type, 'non_terminal) syntax_tree Stack.t =
    Stack.create ()
  in
  let pile_etats = Stack.create () in

  Stack.push a.automaton.initial_state pile_etats;
  let etat_courant = ref a.automaton.initial_state in

  let nouveau_texte = List.map (fun x -> Token x) texte in

  let rec parse_a_partir
      (text : ('token_type, 'non_terminal) non_terminal_or_token list) :
      ('token_type, 'non_terminal) syntax_tree =
    match text with
    | [] -> failwith "Le token EOF n'aurait pas du être lu"
    | x :: q -> (
        match x with
        | NonTerminalRepr nt ->
            let est_a_eof =
              match q with
              | [ Token { token_type } ] when token_type = eof_symbol -> true
              | _ -> false
            in
            if
              states_equal !etat_courant a.automaton.initial_state
              && nt = axiome && est_a_eof
            then
              let racine = Stack.pop_opt pile_arbres in
              match racine with
              | None ->
                  failwith
                    "État invalide : absence de racine apres lecture du texte"
              | Some racine ->
                  if not (Stack.is_empty pile_arbres) then
                    failwith "Axiome lu alors qu'il restait des arbres"
                  else racine
            else
              let nouvel_etat =
                a.automaton.transition !etat_courant
                  (Hashtbl.find a.non_terminal_mapping nt)
              in

              (etat_courant :=
                 match nouvel_etat with
                 | Some e -> e
                 | _ -> failwith "Impossible de lire !");
              Stack.push !etat_courant pile_etats;
              parse_a_partir q
        | Token t -> (
            let anon_token_type =
              Hashtbl.find a.terminal_mapping t.token_type
            in
            match trouve_reduction_a_faire !etat_courant anon_token_type with
            | None ->
                let nouvel_etat =
                  a.automaton.transition !etat_courant anon_token_type
                in

                (etat_courant :=
                   match nouvel_etat with
                   | Some e -> e
                   | _ ->
                       if t.token_type <> eof_symbol then
                         failwith
                           ("Impossible de lire " ^ t.value ^ " ("
                          ^ string_of_int t.start ^ ")")
                       else
                         failwith
                           ("Lecture du texte terminée sans que l'analyse "
                          ^ "syntaxique n'ait abouti"));
                Stack.push !etat_courant pile_etats;
                (* La ligne suivante ne figure pas dans l’algo du livre *)
                Stack.push (Leaf t) pile_arbres;
                parse_a_partir q
            | Some (anon_nt, regle) ->
                let nt = Hashtbl.find reverse_non_terminal_mapping anon_nt in
                let n = Array.length regle in
                let n_arbres = pop_n pile_arbres n |> List.rev in
                Stack.push (Node (nt, n_arbres)) pile_arbres;
                let _ = pop_n pile_etats n in
                etat_courant := Stack.top pile_etats;
                parse_a_partir (NonTerminalRepr nt :: text)))
  in
  parse_a_partir nouveau_texte

(*************************** Fonctions d’affichage ***************************)
let string_of_symbol (s : (char, char) grammar_entry) : string =
  match s with Terminal c | NonTerminal c -> string_of_char c

let string_of_situation
    (((n, derivation, idx), sigma) : anonymized_lr1_situation) : string =
  let ns = string_of_int n in
  let rule_chars = Array.to_list derivation |> List.map string_of_int in
  let rule_beginning = String.concat "" (list_beginning rule_chars idx) in
  let rule_end = String.concat "" (list_skip rule_chars idx) in
  let sigma_list = ref [] in
  BitSet.iter (fun t -> sigma_list := t :: !sigma_list) sigma;
  let sigma_s =
    List.to_seq !sigma_list |> List.of_seq |> List.map string_of_int
    |> String.concat ", "
  in
  ns ^ " -> " ^ rule_beginning ^ "^" ^ rule_end ^ " ~ {" ^ sigma_s ^ "}"

let string_of_state (s : lr1_automaton_state) : string =
  let strings =
    Hashtbl.to_seq s |> List.of_seq |> List.map string_of_situation
  in
  "(" ^ String.concat ", " strings ^ ")"

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
