open Parser

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
