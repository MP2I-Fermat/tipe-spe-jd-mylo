open Regex
open Lexer
open Parser
open Regex_grammar

type grammar_token_type =
  | Terminal_pattern
  | Derivation_symbol
  | Rule_identifier
  | Whitespace
  | Newline
  | Eof

type grammar_node_type =
  | Grammar
  | Grammar_entry
  | Terminal_definition
  | Rule_identifier_list
  | NonTerminal_definition

let grammar_token_rules =
  [
    ( Concatenation
        ( Concatenation (Symbol ':', Symbol '='),
          Empty |> add_character_range ' ' '~' ),
      Terminal_pattern );
    ( Concatenation (Concatenation (Symbol '-', Symbol '>'), Symbol ' '),
      Derivation_symbol );
    ( Regex.Empty
      |> add_character_range 'A' 'Z'
      |> add_character_range 'a' 'z'
      |> add_character '_',
      Rule_identifier );
    (Concatenation (Symbol ' ', Star (Symbol ' ')), Whitespace);
    (Symbol '\n', Newline);
  ]

let grammar_rules =
  [
    (Grammar, [ NonTerminal Grammar_entry ]);
    (Grammar, [ NonTerminal Grammar; NonTerminal Grammar_entry ]);
    (* Allow empty lines *)
    (Grammar_entry, [ Terminal Newline ]);
    (Grammar_entry, [ NonTerminal Terminal_definition; Terminal Newline ]);
    (Grammar_entry, [ NonTerminal NonTerminal_definition; Terminal Newline ]);
    ( Terminal_definition,
      [ Terminal Rule_identifier; Terminal Terminal_pattern ] );
    ( NonTerminal_definition,
      [
        Terminal Rule_identifier;
        Terminal Derivation_symbol;
        NonTerminal Rule_identifier_list;
      ] );
    (Rule_identifier_list, [ Terminal Rule_identifier ]);
    ( Rule_identifier_list,
      [ NonTerminal Rule_identifier_list; Terminal Rule_identifier ] );
  ]

let grammar_of_syntax_tree
    (tree : (grammar_token_type, grammar_node_type) syntax_tree) :
    (char regex * string) list * (string, string) grammar =
  let strip_prefix_from_terminal_pattern (pattern : string) : string =
    String.sub pattern 2 (String.length pattern - 2)
  in

  let build_terminal_definition
      (definition : (grammar_token_type, grammar_node_type) syntax_tree) :
      char regex * string =
    match definition with
    | Node
        ( Terminal_definition,
          [
            Leaf { token_type = Rule_identifier; value = name };
            Leaf { token_type = Terminal_pattern; value = pattern };
          ] ) ->
        (parse_regex (strip_prefix_from_terminal_pattern pattern), name)
    | _ -> failwith "Not a terminal definition"
  in

  let rec build_identifier_list
      (tree : (grammar_token_type, grammar_node_type) syntax_tree)
      (result : string list) : string list =
    match tree with
    | Node
        (Rule_identifier_list, [ Leaf { token_type = Rule_identifier; value } ])
      ->
        value :: result
    | Node
        ( Rule_identifier_list,
          [
            (Node (Rule_identifier_list, _) as remaining);
            Leaf { token_type = Rule_identifier; value };
          ] ) ->
        build_identifier_list remaining (value :: result)
    | _ -> failwith "Not an identifier list"
  in

  let build_non_terminal_definition
      (definition : (grammar_token_type, grammar_node_type) syntax_tree) :
      string * string list =
    match definition with
    | Node
        ( NonTerminal_definition,
          [
            Leaf { token_type = Rule_identifier; value = name };
            Leaf { token_type = Derivation_symbol };
            (Node (Rule_identifier_list, _) as identifier_list);
          ] ) ->
        (name, build_identifier_list identifier_list [])
    | _ -> failwith "Not a nonterminal definition"
  in

  let process_entry
      (entry : (grammar_token_type, grammar_node_type) syntax_tree)
      (token_rules : (char regex * string) list)
      (grammar_rules : (string * string list) list) =
    match entry with
    | Node (Grammar_entry, [ Leaf { token_type = Newline } ]) ->
        (token_rules, grammar_rules)
    | Node
        ( Grammar_entry,
          [
            (Node (Terminal_definition, _) as definition);
            Leaf { token_type = Newline };
          ] ) ->
        let terminal_definition = build_terminal_definition definition in
        if
          List.find_opt
            (fun (_, name) -> name = snd terminal_definition)
            token_rules
          <> None
        then
          failwith ("Duplicate definition for token: " ^ snd terminal_definition)
        else (terminal_definition :: token_rules, grammar_rules)
    | Node
        ( Grammar_entry,
          [
            (Node (NonTerminal_definition, _) as definition);
            Leaf { token_type = Newline };
          ] ) ->
        (token_rules, build_non_terminal_definition definition :: grammar_rules)
    | _ -> failwith "Not a grammar entry"
  in

  let rec build_result_from
      (tree : (grammar_token_type, grammar_node_type) syntax_tree)
      (token_rules : (char regex * string) list)
      (grammar_rules : (string * string list) list) =
    match tree with
    | Node (Grammar, [ entry ]) -> process_entry entry token_rules grammar_rules
    | Node (Grammar, [ others; entry ]) ->
        let token_rules', grammar_rules' =
          process_entry entry token_rules grammar_rules
        in
        build_result_from others token_rules' grammar_rules'
    | _ -> failwith "Not a grammar"
  in

  let token_rules, raw_grammar_rules = build_result_from tree [] [] in

  let convert_identifier (identifier : string) : (string, string) grammar_entry
      =
    if List.find_opt (fun (_, name) -> name = identifier) token_rules <> None
    then Terminal identifier
    else if
      List.find_opt (fun (name, _) -> name = identifier) raw_grammar_rules
      <> None
    then NonTerminal identifier
    else failwith ("No rule matching: " ^ identifier)
  in

  let grammar_rules =
    List.map
      (fun (name, raw_derivation) ->
        (name, List.map convert_identifier raw_derivation))
      raw_grammar_rules
  in

  (token_rules, grammar_rules)

let parse_grammar (s : string) =
  let tokens = tokenize grammar_token_rules Eof s in
  let tokens_no_whitespace =
    List.filter (fun token -> token.token_type <> Whitespace) tokens
  in
  let syntax_tree = parse grammar_rules tokens_no_whitespace in
  grammar_of_syntax_tree syntax_tree
