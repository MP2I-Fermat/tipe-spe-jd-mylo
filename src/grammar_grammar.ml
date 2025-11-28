open Regex
open Lexer
open Parser
open Regex_grammar
open Utils

type grammar_token_type =
  | Terminal_pattern
  | Derivation_symbol
  | Identifier
  | Question
  | Whitespace
  | Newline
  | Comment_start
  | Unrecognizable
  | Eof

type grammar_node_type =
  | Grammar
  | Grammar_entry
  | Terminal_definition
  | Rule_identifier_list
  | Rule_identifier_list_entry
  | NonTerminal_definition

let grammar_token_rules =
  [
    ( Concatenation
        ( Concatenation (Symbol (u ':'), Symbol (u '=')),
          Regex.Star (Empty |> add_character_range_c ' ' '~') ),
      Terminal_pattern );
    ( Concatenation (Concatenation (Symbol (u '-'), Symbol (u '>')),
                     Symbol (u ' ')),
      Derivation_symbol );
    ( Regex.Concatenation
        ( Regex.Empty
          |> add_character_range_c 'A' 'Z'
          |> add_character_range_c 'a' 'z'
          |> add_character_range_c '0' '9'
          |> add_character_c '_',
          Regex.Star
            (Regex.Empty
            |> add_character_range_c 'A' 'Z'
            |> add_character_range_c 'a' 'z'
            |> add_character_range_c '0' '9'
            |> add_character_c '_') ),
      Identifier );
    (Concatenation (Symbol (u ' '), Star (Symbol (u ' '))), Whitespace);
    (Symbol (u '\n'), Newline);
    (Symbol (u '?'), Question);
    (Symbol (u '#'), Comment_start);
    ( Regex.Empty |> add_character_range_c (char_of_int 0) (char_of_int 255),
      Unrecognizable );
  ]

let grammar_rules =
  grammar_of_rule_list
    [
      (Grammar, [ NonTerminal Grammar_entry ]);
      (Grammar, [ NonTerminal Grammar; NonTerminal Grammar_entry ]);
      (* Allow empty lines *)
      (Grammar_entry, [ Terminal Newline ]);
      (Grammar_entry, [ NonTerminal Terminal_definition; Terminal Newline ]);
      (Grammar_entry, [ NonTerminal NonTerminal_definition; Terminal Newline ]);
      (Terminal_definition, [ Terminal Identifier; Terminal Terminal_pattern ]);
      ( NonTerminal_definition,
        [
          Terminal Identifier;
          Terminal Derivation_symbol;
          NonTerminal Rule_identifier_list;
        ] );
      (Rule_identifier_list, [ NonTerminal Rule_identifier_list_entry ]);
      ( Rule_identifier_list,
        [
          NonTerminal Rule_identifier_list_entry;
          NonTerminal Rule_identifier_list;
        ] );
      (Rule_identifier_list_entry, [ Terminal Identifier ]);
      (Rule_identifier_list_entry, [ Terminal Identifier; Terminal Question ]);
    ]

let grammar_of_syntax_tree
    (tree : (grammar_token_type, grammar_node_type) syntax_tree) :
    (uchar regex * string) list * (string, string) grammar =
  let strip_prefix_from_terminal_pattern (pattern : string) : string =
    let rec non_space_index (i : int) =
      if i = String.length pattern - 1 then i
      else if pattern.[i] <> ' ' then i
      else non_space_index (i + 1)
    in
    let start = non_space_index 2 in
    String.sub pattern start (String.length pattern - start)
  in

  let build_terminal_definition
      (definition : (grammar_token_type, grammar_node_type) syntax_tree) :
      uchar regex * string =
    match definition with
    | Node
        ( Terminal_definition,
          [
            Leaf { token_type = Identifier; value = name };
            Leaf { token_type = Terminal_pattern; value = pattern };
          ] ) -> (
        let raw_pattern = strip_prefix_from_terminal_pattern pattern in
        try (parse_regex raw_pattern, name)
        with Failure s ->
          failwith ("Failed to parse regex " ^ raw_pattern ^ ": " ^ s))
    | _ -> failwith "Not a terminal definition"
  in

  let build_identifier_list
      (tree : (grammar_token_type, grammar_node_type) syntax_tree) :
      string list list =
    let rec build_into_rev
        (tree : (grammar_token_type, grammar_node_type) syntax_tree)
        (res : string list list) =
      match tree with
      | Node
          ( Rule_identifier_list,
            [
              Node
                ( Rule_identifier_list_entry,
                  [ Leaf { token_type = Identifier; value } ] );
            ] ) ->
          List.map (fun r -> value :: r) res
      | Node
          ( Rule_identifier_list,
            [
              Node
                ( Rule_identifier_list_entry,
                  [
                    Leaf { token_type = Identifier; value };
                    Leaf { token_type = Question };
                  ] );
            ] ) ->
          List.rev_append (List.map (fun r -> value :: r) res) res
      | Node
          ( Rule_identifier_list,
            [
              Node
                ( Rule_identifier_list_entry,
                  [ Leaf { token_type = Identifier; value } ] );
              remaining;
            ] ) ->
          build_into_rev remaining (List.map (fun r -> value :: r) res)
      | Node
          ( Rule_identifier_list,
            [
              Node
                ( Rule_identifier_list_entry,
                  [
                    Leaf { token_type = Identifier; value };
                    Leaf { token_type = Question };
                  ] );
              remaining;
            ] ) ->
          build_into_rev remaining
            (List.rev_append (List.map (fun r -> value :: r) res) res)
      | _ -> failwith "Not an identifier list"
    in
    List.map List.rev (build_into_rev tree [ [] ])
  in

  let build_non_terminal_definition
      (definition : (grammar_token_type, grammar_node_type) syntax_tree) :
      string * string list list =
    match definition with
    | Node
        ( NonTerminal_definition,
          [
            Leaf { token_type = Identifier; value = name };
            Leaf { token_type = Derivation_symbol };
            (Node (Rule_identifier_list, _) as identifier_list);
          ] ) ->
        (name, build_identifier_list identifier_list)
    | _ -> failwith "Not a nonterminal definition"
  in

  let process_entry
      (entry : (grammar_token_type, grammar_node_type) syntax_tree)
      (token_rules : (uchar regex * string) list)
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
        let name, derivations = build_non_terminal_definition definition in

        ( token_rules,
          List.rev_append
            (List.map (fun d -> (name, d)) derivations)
            grammar_rules )
    | _ -> failwith "Not a grammar entry"
  in

  let rec build_result_from
      (tree : (grammar_token_type, grammar_node_type) syntax_tree)
      (token_rules : (uchar regex * string) list)
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

  (token_rules, grammar_of_rule_list grammar_rules)

let parse_grammar (s : string) =
  let tokens = tokenize grammar_token_rules Eof s in
  let tokens_no_whitespace =
    List.filter (fun token -> token.token_type <> Whitespace) tokens
  in

  let rec remove_comments (tokens : grammar_token_type token list)
      (in_comment : bool) (res : grammar_token_type token list) :
      grammar_token_type token list =
    match tokens with
    | [] -> res
    | { token_type = Comment_start } :: q -> remove_comments q true res
    | ({ token_type = Newline } as x) :: q -> remove_comments q false (x :: res)
    | x :: q ->
        let next_res = if in_comment then res else x :: res in
        remove_comments q in_comment next_res
  in

  let tokens_clean = List.rev (remove_comments tokens_no_whitespace false []) in
  let automaton = construit_automate_LR1 grammar_rules Grammar Eof in
  let syntax_tree = parse automaton Eof tokens_clean Grammar in
  grammar_of_syntax_tree syntax_tree
