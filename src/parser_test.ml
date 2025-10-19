open Parser
open Automaton
open Utils

let test_premier_LL1 =
  let grammaire1 (* page 123, exemple 144 *) =
    [ ('S', [ Terminal 'a'; NonTerminal 'T' ]); ('T', [ Terminal 'b' ]) ]
  in
  assert (
    Hashset.equals
      (premier_LL1 [ Terminal 'a'; NonTerminal 'T' ] grammaire1)
      (Hashset.of_list [ 'a' ]));
  assert (
    Hashset.equals
      (premier_LL1 [ NonTerminal 'T' ] grammaire1)
      (Hashset.of_list [ 'b' ]));

  let grammaire2 (* page 60, exemple 24 *) =
    [
      ('S', [ NonTerminal 'U' ]);
      ('S', [ NonTerminal 'V' ]);
      ('U', [ Terminal 'a'; Terminal 'b' ]);
      ('V', [ Terminal 'c'; Terminal 'd' ]);
    ]
  in
  assert (
    Hashset.equals
      (premier_LL1 [ Terminal 'a'; Terminal 'b' ] grammaire2)
      (Hashset.of_list [ 'a' ]));
  assert (
    Hashset.equals
      (premier_LL1 [ Terminal 'c'; Terminal 'd' ] grammaire2)
      (Hashset.of_list [ 'c' ]));
  assert (
    Hashset.equals
      (premier_LL1 [ NonTerminal 'U' ] grammaire2)
      (Hashset.of_list [ 'a' ]));
  assert (
    Hashset.equals
      (premier_LL1 [ NonTerminal 'V' ] grammaire2)
      (Hashset.of_list [ 'c' ]));
  assert (
    Hashset.equals
      (premier_LL1 [ NonTerminal 'S' ] grammaire2)
      (Hashset.of_list [ 'a'; 'c' ]));

  let grammaire_gpost =
    (* Page 67, exemple 40 *)
    [
      ('S', [ NonTerminal 'S'; NonTerminal 'S'; Terminal '+' ]);
      ('S', [ Terminal 'c' ]);
    ]
  in
  assert (
    Hashset.equals
      (premier_LL1
         [ NonTerminal 'S'; NonTerminal 'S'; Terminal '+' ]
         grammaire_gpost)
      (Hashset.of_list [ 'c' ]))

let test_regroupe_union : unit =
  (match
     regroupe_union
       [
         ('a', 'a', Hashset.of_list [ 1; 2 ]);
         ('b', 'b', Hashset.of_list [ 3 ]);
         ('a', 'a', Hashset.of_list [ 4; 2 ]);
       ]
   with
  | [ ('a', 'a', s1); ('b', 'b', s2) ]
    when Hashset.equals s1 (Hashset.of_list [ 1; 2; 4 ])
         && Hashset.equals s2 (Hashset.singleton 3) ->
      ()
  | _ -> assert false);

  assert (regroupe_union [] = [])

(* let test_fermeture_situations_LR1 : unit =
  (* Dans les examples suivants, les symboles « drapeau » dans le livre sont
   * représentés par le caractère 'e' (pour “end of file”) *)
  (* page 123, example 148 *)
  let regle1 = ('S', [ Terminal 'a'; NonTerminal 'T'; Terminal 'c' ]) in
  let regle2 = ('T', [ Terminal 'b' ]) in
  let g = [ regle1; regle2 ] in
  let situation1 = (regle1, 0, Hashset.singleton 'e') in
  let situation2 = (regle1, 1, Hashset.singleton 'e') in
  let situation3 = (regle2, 0, Hashset.singleton 'c') in

  let state1 = Hashtbl.create 2 in
  Hashtbl.replace state1 (regle1, 0) (Hashset.singleton 'e');
  fermer_situations_LR1 state1 g

  assert (fermeture_situations_LR1 [ situation1 ] g = [ situation1 ]);
  assert (fermeture_situations_LR1 [ situation2 ] g = [ situation2; situation3 ]);
  (* page 124, example 149 *)
  let regle1 = ('S', [ Terminal 'a'; NonTerminal 'T'; NonTerminal 'U' ]) in
  let regle2 = ('T', [ Terminal 'b' ]) in
  let regle3 = ('U', [ Terminal 'c' ]) in
  let g = [ regle1; regle2; regle3 ] in
  let situation1 = (regle1, 0, Hashset.singleton 'e') in
  let situation2 = (regle1, 1, Hashset.singleton 'e') in
  let situation3 = (regle2, 0, Hashset.singleton 'c') in
  assert (fermeture_situations_LR1 [ situation1 ] g = [ situation1 ]);
  assert (fermeture_situations_LR1 [ situation2 ] g = [ situation2; situation3 ]);
  (* Ensemble vide *)
  assert (fermeture_situations_LR1 [] [] = []) *)

let test_construit_automate_LR1 : unit =
  let regle1 = ('S', [ Terminal 'i' ]) in
  let regle2 =
    ('S', [ Terminal 'i'; Terminal '['; Terminal 'c'; Terminal ']' ])
  in
  let g = [ regle1; regle2 ] in
  let eof = 'e' in
  let situation11 = (regle1, 0, Hashset.singleton eof) in
  let situation12 = (regle2, 0, Hashset.singleton eof) in
  let situation21 = (regle1, 1, Hashset.singleton eof) in
  let situation22 = (regle2, 1, Hashset.singleton eof) in
  let situation3 = (regle2, 2, Hashset.singleton eof) in
  let situation4 = (regle2, 3, Hashset.singleton eof) in
  let situation5 = (regle2, 4, Hashset.singleton eof) in
  let etat1 = [ situation11; situation12 ] in
  let etat2 = [ situation21; situation22 ] in
  let etat3 = [ situation3 ] in
  let etat4 = [ situation4 ] in
  let etat5 = [ situation5 ] in
  let etats = List.sort compare [ etat1; etat2; etat3; etat4; etat5 ] in
  let transitions =
    List.sort compare
      [
        (etat1, Terminal 'i', etat2);
        (etat2, Terminal '[', etat3);
        (etat3, Terminal 'c', etat4);
        (etat4, Terminal ']', etat5);
      ]
  in
  let a =
    {
      states = etats;
      initial_states = [ etat1 ];
      final_states = [];
      transitions;
    }
  in
  (* We can't directly inspect the underlying states. Instead just check that we have the same number of states. *)
  assert (
    Hashset.length (construit_automate_LR1 g 'S' eof).states
    = List.length a.states)

let test_trouve_conflit =
  let grammar_with_conflict =
    [
      ('S', [ NonTerminal 'A' ]);
      ('A', [ NonTerminal 'V'; Terminal '='; NonTerminal 'E' ]);
      ('S', [ NonTerminal 'C'; Terminal ':'; Terminal 'a' ]);
      ('C', [ NonTerminal 'E'; Terminal '='; NonTerminal 'E' ]);
      ('V', [ Terminal 'i' ]);
      ('E', [ Terminal 'i' ]);
    ]
  in
  let automaton_with_conflict =
    construit_automate_LR1 grammar_with_conflict 'S' '_'
  in
  match trouve_conflits automaton_with_conflict with
  | None -> failwith "No conflict found"
  | Some _ ->
      ();

      let grammar_without_conflicts =
        [ ('S', [ Terminal 'a' ]); ('S', [ Terminal 'a'; Terminal 'b' ]) ]
      in
      let automaton_without_conflicts =
        construit_automate_LR1 grammar_without_conflicts 'S' '_'
      in
      if trouve_conflits automaton_without_conflicts <> None then
        failwith "Conflict found"
