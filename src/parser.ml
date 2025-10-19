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

type ('token_type, 'non_terminal) lr0_situation =
  ('token_type, 'non_terminal) rule * int

(* Dictionnaire de situations LR(0) a leurs ensembles premiers correspondants.
   On assure de cette façon l’unicité de la situation pour une règle donnee
   dans les états des automates LR(1). *)
type ('token_type, 'non_terminal) lr1_automaton_state =
  (('token_type, 'non_terminal) lr0_situation, 'token_type Hashset.t) Hashtbl.t

(* Représente un automate LR(1) *)
type ('token_type, 'non_terminal) lr1_automaton =
  ( ('token_type, 'non_terminal) grammar_entry,
    ('token_type, 'non_terminal) lr1_automaton_state )
  deterministic_automaton

type ('token_type, 'non_terminal) lr1_transition =
  ('token_type, 'non_terminal) lr1_automaton_state
  * ('token_type, 'non_terminal) grammar_entry
  * ('token_type, 'non_terminal) lr1_automaton_state

(* Renvoie l’ensemble Premier_LL(1)(s) dans la grammaire g *)
let premier_LL1 (s : ('token_type, 'non_terminal) derivation)
    (g : ('token_type, 'non_terminal) grammar)
    (cache :
      (('token_type, 'non_terminal) derivation, 'token_type Hashset.t) Hashtbl.t)
    : 'token_type Hashset.t =
  (* Crée un dictionnaire d tel que d[s] est l'ensemble des derivations w tels
     que premier(s) est inclus dans premier(w).
     cf. 4.2.1.3 Théorème 32 (p 63). *)
  let construire_inclusions () :
      ( ('token_type, 'non_terminal) derivation,
        ('token_type, 'non_terminal) derivation Hashset.t )
      Hashtbl.t =
    let inclusions = Hashtbl.create 2 in
    let a_traiter = Hashset.create () in
    Hashtbl.replace inclusions s (Hashset.create ());
    Hashset.add a_traiter s;

    while not (Hashset.is_empty a_traiter) do
      let derivation = Hashset.remove_one a_traiter in
      if Hashtbl.find_opt cache derivation = None then
        let derivation_contient =
          match derivation with
          | [ Terminal _ ] -> []
          | [ NonTerminal n ] ->
              List.filter_map (fun (n', d) -> if n = n' then Some d else None) g
          | x :: q -> [ [ x ] ]
          | [] -> failwith "Cannot compute premier_LL1 of an empty derivation"
        in
        derivation_contient
        |> List.iter (fun derivation_contenue ->
               match Hashtbl.find_opt inclusions derivation_contenue with
               | Some sur_derivations -> Hashset.add sur_derivations derivation
               | None ->
                   let sur_derivations = Hashset.create () in
                   Hashset.add sur_derivations derivation;
                   Hashtbl.replace inclusions derivation_contenue
                     sur_derivations;
                   (* C'est une derivation jusqu'ici inconnue. *)
                   Hashset.add a_traiter derivation_contenue)
    done;

    inclusions
  in

  let inclusions = construire_inclusions () in
  let valeurs = Hashtbl.create (Hashtbl.length inclusions) in

  let a_traiter = Hashset.create () in

  (* Initialisation *)
  Hashtbl.iter
    (fun k v ->
      let premier_k = Hashset.create () in
      Hashtbl.replace valeurs k premier_k;
      match k with
      | [ Terminal a ] ->
          Hashset.add premier_k a;
          Hashset.add a_traiter k
      | _ -> (
          match Hashtbl.find_opt cache k with
          | None -> ()
          | Some premier ->
              Hashtbl.replace valeurs k premier;
              Hashset.add a_traiter k))
    inclusions;

  (* Saturation *)
  while not (Hashset.is_empty a_traiter) do
    let derivation = Hashset.remove_one a_traiter in
    let valeur_derivation = Hashtbl.find valeurs derivation in
    let sur_derivations = Hashtbl.find inclusions derivation in
    Hashset.iter
      (fun sur_derivation ->
        let valeur_sur_derivation = Hashtbl.find valeurs sur_derivation in
        let longueur_init = Hashset.length valeur_sur_derivation in
        Hashset.iter (Hashset.add valeur_sur_derivation) valeur_derivation;

        (* Si l'ajout des elements de valeur_derivation a change la
           valeur de valeur_sur_derivation, alors il faut re-traiter
           sur_derivation. *)
        if longueur_init <> Hashset.length valeur_sur_derivation then
          Hashset.add a_traiter sur_derivation)
      sur_derivations
  done;

  Hashtbl.iter (Hashtbl.replace cache) valeurs;

  Hashtbl.find valeurs s

(* Renvoie l’ensemble Premier_LR(1)(s, σ) dans la grammaire g *)
let premier_LR1 (s : ('token_type, 'non_terminal) derivation)
    (sigma : 'token_type Hashset.t) (g : ('token_type, 'non_terminal) grammar)
    (cache :
      (('token_type, 'non_terminal) derivation, 'token_type Hashset.t) Hashtbl.t)
    : 'token_type Hashset.t =
  match s with [] -> sigma | _ -> premier_LL1 s g cache

(* Sature e jusqu'a que e soit une fermeture des situations LR(1) de e. *)
let fermer_situations_LR1 (e : ('token_type, 'non_terminal) lr1_automaton_state)
    (g : ('token_type, 'non_terminal) grammar) : unit =
  (* Si le non-terminal de regle est nt, renvoie la situation nt->^γ~σ2.
   * Renvoie None sinon *)
  let nouvelle_situation_regle (nt : 'non_terminal)
      (sigma2 : 'token_type Hashset.t)
      (regle : ('token_type, 'non_terminal) rule) :
      (('token_type, 'non_terminal) lr0_situation * 'token_type Hashset.t)
      option =
    if fst regle = nt then Some ((regle, 0), Hashset.copy sigma2) else None
  in

  let premier_cache = Hashtbl.create 2 in

  (* Sachant une situation s: N -> α^Tβ~σ avec T un non-terminal, renvoie
   * la liste des situations T->^γ~premierLR1(β, σ) pour T->γ règle de g *)
  let liste_nouvelles_situations
      (((_, derivation), curseur) : ('token_type, 'non_terminal) lr0_situation)
      (sigma : 'token_type Hashset.t) :
      (('token_type, 'non_terminal) lr0_situation * 'token_type Hashset.t) list
      =
    let regle_fin = list_skip derivation curseur in
    match regle_fin with
    | NonTerminal nt :: beta ->
        let premier = premier_LR1 beta sigma g premier_cache in
        List.filter_map (nouvelle_situation_regle nt premier) g
    | _ -> []
  in

  let a_traiter = Hashset.create () in
  Hashtbl.iter (fun k _ -> Hashset.add a_traiter k) e;

  while not (Hashset.is_empty a_traiter) do
    let situation = Hashset.remove_one a_traiter in
    let sigma = Hashtbl.find e situation in
    let nouvelles_situations = liste_nouvelles_situations situation sigma in
    List.iter
      (fun (nouvelle_situation, nouveau_premier) ->
        match Hashtbl.find_opt e nouvelle_situation with
        | None ->
            (* La derivation T -> ^gamma n’était pas présente dans e. *)
            Hashtbl.replace e nouvelle_situation nouveau_premier;
            Hashset.add a_traiter nouvelle_situation
        | Some premier ->
            let longueur_init = Hashset.length premier in
            Hashset.iter (Hashset.add premier) nouveau_premier;
            if longueur_init <> Hashset.length premier then
              (* On a ajouté des elements a l'ensemble sigma de T -> ^gamma *)
              Hashset.add a_traiter nouvelle_situation)
      nouvelles_situations
  done

let states_equal (a : ('token_type, 'non_terminal) lr1_automaton_state)
    (b : ('token_type, 'non_terminal) lr1_automaton_state) =
  a == b
  ||
  if Hashtbl.length a <> Hashtbl.length b then false
  else
    Hashtbl.to_seq a
    |> Seq.for_all (fun (k, v) ->
           match Hashtbl.find_opt b k with
           | None -> false
           | Some v' -> Hashset.equals v v')

(* Construit l’automate LR(1) de la grammaire g. eof_token désigne le lexème
 * de fin de fichier, il ne doit pas être utilisé dans les règles de la
 * grammaire (mais il devra figurer dans la sortie de l’analyseur lexical) *)
let construit_automate_LR1 (g : ('token_type, 'non_terminal) grammar)
    (axiome : 'non_terminal) (lexeme_eof : 'token_type) :
    ('token_type, 'non_terminal) lr1_automaton =
  (* On veut pouvoir mettre des états de l'automate LR(1) dans un dictionnaire.
     Cela facilite non seulement la construction de l'automate mais rend aussi
     son execution plus efficace.
  
     Malheureusement, les états LR(1) ne sont pas compatibles avec le module
     Hashtbl d'OCaml tel quels: ils contiennent des Hashset.t, dont l'egalite
     (i.e Hashset.equals) n'est pas l’identité structurelle (deux Hashtbl.t
     peuvent contenir les memes elements mais ne pas avoir le meme nombre de
     buckets, par exemple).
  
     In faut donc nous munir d'un Hashtbl avec une fonction de hachage et
     d'egalite que nous contrôlons, ce qui est possible via le functor
     Hashtbl.Make.
  
     Deuxième malheur, nos états LR(1) sont génériques, et le type HashedType.t
     ne peut pas l’être. Nous devons donc masquer les paramètres de type de
     lr1_automaton_state dans notre Hashtbl.
  
     Cela est possible grace a l'usage de GADT.
  
     Cela mène a deux problèmes de plus:
     - Le type de notre Hashtbl doit être un GADT. Il ne peut donc pas directement
       être un lr1_automaton_state, mais est plutôt un variant d'un type contenant
       un lr1_automaton_state.
     - Comme nous masquons les paramètres de type de toutes les clés de notre
       Hashtbl, OCaml n'apporte aucune garantie quand au type exact des objets
       extraits de notre Hashtbl: c'est a nous de s'assurer que nous n’insérons et
       n’extrayons que des objets du meme type. Il faut alors utiliser Obj.magic
       pour éviter les erreurs de type.
  
     Ces modules sont restreints a la fonction construit_automate_LR1 pour ces
     raisons.
  *)
  let module AnyLR1State = struct
    type t = Any : (_, _) lr1_automaton_state -> t

    let equal (Any a) (Any b) = states_equal (Obj.magic a) (Obj.magic b)
    let hash (Any a) = Hashtbl.fold (fun k _ acc -> acc lxor Hashtbl.hash k) a 0
  end in
  let module LR1StateMap = struct
    include Hashtbl.Make (AnyLR1State)

    let remove_one (t : 'a t) : ('non_terminal, 'token_type) lr1_automaton_state
        =
      match (to_seq_keys t) () with
      | Nil -> raise (Invalid_argument "Cannot remove from an empty set")
      | Cons (key, _) -> (
          remove t key;
          match key with Any a -> Obj.magic a)
  end in
  (* Étant donné une liste l de situations LR(1), renvoie la liste des terminaux
   * et non terminaux pouvant être lus. *)
  let rec liste_terminaux_et_non_terminaux_a_iterer
      (s : ('token_type, 'non_terminal) lr1_automaton_state) :
      ('token_type, 'non_terminal) grammar_entry Hashset.t =
    let res = Hashset.create () in
    Hashtbl.iter
      (fun ((_, regle), curseur) _ ->
        if curseur <> List.length regle then
          let alpha = List.nth regle curseur in
          Hashset.add res alpha)
      s;
    res
  in

  (* On ajoute toutes les règles pour l'axiome, puis on ferme l'ensemble pour obtenir l’état initial. *)
  let etat_initial = Hashtbl.create 2 in
  List.iter
    (fun (nt, derivation) ->
      if nt = axiome then
        Hashtbl.replace etat_initial
          ((nt, derivation), 0)
          (Hashset.singleton lexeme_eof))
    g;
  fermer_situations_LR1 etat_initial g;

  (* transitions[state0][symbol] est l’état atteint en lisant symbol depuis state0. *)
  let transitions = LR1StateMap.create 2 in
  (* Collection des états crées. *)
  let etats = Hashset.create () in

  (* Ensemble des états a traiter, sous forme d'un dictionnaires d’états a unit. *)
  let a_traiter = LR1StateMap.create 2 in
  LR1StateMap.replace a_traiter (AnyLR1State.Any etat_initial) ();

  while LR1StateMap.length a_traiter <> 0 do
    let etat = LR1StateMap.remove_one a_traiter in
    Hashset.add etats etat;
    (* Les transitions sortants de cet état. *)
    let transitions_etat = Hashtbl.create 2 in
    LR1StateMap.replace transitions (AnyLR1State.Any etat) transitions_etat;
    let tnt = liste_terminaux_et_non_terminaux_a_iterer etat in
    Hashset.iter
      (fun alpha ->
        let nouvel_etat = Hashtbl.create 2 in

        Hashtbl.iter
          (fun ((nt, derivation), curseur) v ->
            if
              curseur <> List.length derivation
              && List.nth derivation curseur = alpha
            then
              Hashtbl.replace nouvel_etat
                ((nt, derivation), curseur + 1)
                (Hashset.copy v))
          etat;

        fermer_situations_LR1 nouvel_etat g;

        Hashtbl.replace transitions_etat alpha nouvel_etat;

        if LR1StateMap.find_opt transitions (AnyLR1State.Any nouvel_etat) = None
        then LR1StateMap.replace a_traiter (AnyLR1State.Any nouvel_etat) ())
      tnt
  done;

  {
    states = etats;
    initial_state = etat_initial;
    final_states = Hashset.create ();
    transition =
      (fun state0 symbol ->
        let transitions_state0 =
          LR1StateMap.find transitions (AnyLR1State.Any state0)
        in
        Hashtbl.find_opt transitions_state0 symbol);
  }

(* Renvoie None si `a` est sans conflits LR(1), et un état de `a` présentant un
 * conflit sinon. *)
let trouve_conflits (a : ('token_type, 'non_terminal) lr1_automaton) :
    ('token_type, 'non_terminal) lr1_automaton_state option =
  let exception Conflit in
  (* Renvoie true ssi `s` est un état LR(1) présentant un conflit. *)
  let est_conflit (s : ('token_type, 'non_terminal) lr1_automaton_state) : bool
      =
    try
      let suivants_a_reduire = Hashset.create () in
      (* Recherche de conflits réduire/réduire *)
      Hashtbl.iter
        (fun ((nt, derivation), curseur) v ->
          if curseur = List.length derivation then (
            if
              not (Hashset.is_empty (Hashset.intersection v suivants_a_reduire))
            then raise Conflit;
            Hashset.iter (Hashset.add suivants_a_reduire) v))
        s;

      (* Recherche de conflits lire/réduire *)
      Hashtbl.iter
        (fun ((_, derivation), curseur) _ ->
          if curseur <> List.length derivation then
            match List.nth derivation curseur with
            | NonTerminal nt -> ()
            | Terminal t ->
                if Hashset.mem suivants_a_reduire t then raise Conflit)
        s;

      false
    with Conflit -> true
  in

  let rec trouve_conflit
      (remaining_states : ('token_type, 'non_terminal) lr1_automaton_state list)
      : ('token_type, 'non_terminal) lr1_automaton_state option =
    match remaining_states with
    | [] -> None
    | s :: q -> if est_conflit s then Some s else trouve_conflit q
  in

  trouve_conflit (Hashset.to_list a.states)

(* À partir d’un état e et d’un terminal t, renvoie une règle que l’on peut
 * réduire (i.e. une situation N->a_1…a_n^ ~ σ où t∈σ) ou None s’il n’y en
 * n’a pas. *)
let rec trouve_reduction_a_faire
    (e : ('token_type, 'non_terminal) lr1_automaton_state) (t : 'token_type) :
    ('token_type, 'non_terminal) rule option =
  (* Renvoie true si la situation s est une situation à réduction, false sinon *)
  let a_reduire (((_, rule), idx) : ('token_type, 'non_terminal) lr0_situation)
      : bool =
    idx = List.length rule
  in

  let situation_a_reduire =
    Hashtbl.to_seq e
    |> seq_find (fun (lr0_situation, sigma) ->
           a_reduire lr0_situation && Hashset.mem sigma t)
  in
  match situation_a_reduire with
  | None -> None
  | Some ((rule, _), _) -> Some rule

let parse (a : ('token_type, 'non_terminal) lr1_automaton)
    (eof_symbol : 'token_type) (texte : 'token_type token list)
    (axiome : 'non_terminal) : ('token_type, 'non_terminal) syntax_tree =
  if trouve_conflits a <> None then
    failwith "L'automate présente des conflits – la grammaire n'est pas LR(1)";
  let pile_arbres : ('token_type, 'non_terminal) syntax_tree Stack.t =
    Stack.create ()
  in
  let pile_etats = Stack.create () in

  Stack.push a.initial_state pile_etats;
  let etat_courant = ref a.initial_state in

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
              states_equal !etat_courant a.initial_state
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
              let nouvel_etat = a.transition !etat_courant (NonTerminal nt) in

              (etat_courant :=
                 match nouvel_etat with
                 | Some e -> e
                 | _ -> failwith "Impossible de lire !");
              Stack.push !etat_courant pile_etats;
              parse_a_partir q
        | Token t -> (
            match trouve_reduction_a_faire !etat_courant t.token_type with
            | None ->
                let nouvel_etat =
                  a.transition !etat_courant (Terminal t.token_type)
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
            | Some (nt, regle) ->
                let n = List.length regle in
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
    ((((n, rule), idx), sigma) : (char, char) lr0_situation * char Hashset.t) :
    string =
  let ns = string_of_char n in
  let rule_chars =
    List.map (fun x -> match x with Terminal c | NonTerminal c -> c) rule
  in
  let rule_beginning = implode (list_beginning rule_chars idx) in
  let rule_end = implode (list_skip rule_chars idx) in
  let sigma_s =
    Hashset.to_list sigma |> List.map string_of_char |> String.concat ", "
  in
  ns ^ " -> " ^ rule_beginning ^ "^" ^ rule_end ^ " ~ {" ^ sigma_s ^ "}"

let string_of_state (s : (char, char) lr1_automaton_state) : string =
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
