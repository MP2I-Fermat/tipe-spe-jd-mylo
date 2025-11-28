open Regex
open Lexer
open Parser
open Utils

type regex_token_type =
  | Open_paren
  | Close_paren
  | Open_bracket
  | Close_bracket
  | Or
  | Plus
  | Star
  | Question
  | Escape
  | Character
  | Eof


let add_character (c : uchar) (r : uchar regex) : uchar regex =
  Regex.Union (r, Regex.Symbol c)

let add_character_c (c : char) (r: uchar regex) : uchar regex =
  add_character (u c) r


let rec add_character_range (start : uchar) (last : uchar) (r : uchar regex) =
  if start > last then failwith "Invalid range";
  if start = last then add_character start r
  else
    add_character_range
      (Uchar.of_int (Uchar.to_int start + 1))
      last (add_character start r)

let add_character_range_c (start: char) (last: char) (r: uchar regex) =
  add_character_range (u start) (u last) r


let regex_token_rules =
  [
    (Regex.Symbol (u '('), Open_paren);
    (Regex.Symbol (u ')'), Close_paren);
    (Regex.Symbol (u '['), Open_bracket);
    (Regex.Symbol (u ']'), Close_bracket);
    (Regex.Symbol (u '|'), Or);
    (Regex.Symbol (u '*'), Star);
    (Regex.Symbol (u '+'), Plus);
    (Regex.Symbol (u '?'), Question);
    ( Regex.Concatenation
        ( Regex.Symbol (u '\\'),
          Regex.Empty |> add_character_c '(' |> add_character_c ')'
          |> add_character_c '|' |> add_character_c '*' |> add_character_c '\\'
          |> add_character_c 'n' |> add_character_c 't' |> add_character_c 'r'
          |> add_character_c '[' |> add_character_c ']' |> add_character_c '+'
          |> add_character_c '?' ),
      Escape );
    ( Regex.Empty
      |> add_character_range_c ' ' '\''
      (* (, ), * *)
      |> add_character_range_c '+' '{'
      (* | *)
      |> add_character_range_c '}' '~',
      Character );
  ]

type regex_rule =
  | Regex_union
  | Regex_concatenation
  | Regex_primitive
  | Character_class
  | Character_class_entry

let regex_grammar =
  grammar_of_rule_list
    [
      (Regex_union, [ NonTerminal Regex_concatenation ]);
      ( Regex_union,
        [
          NonTerminal Regex_concatenation; Terminal Or; NonTerminal Regex_union;
        ] );
      (Regex_concatenation, [ NonTerminal Regex_primitive ]);
      ( Regex_concatenation,
        [ NonTerminal Regex_primitive; NonTerminal Regex_concatenation ] );
      (Regex_primitive, [ NonTerminal Regex_primitive; Terminal Star ]);
      (Regex_primitive, [ NonTerminal Regex_primitive; Terminal Plus ]);
      (Regex_primitive, [ NonTerminal Regex_primitive; Terminal Question ]);
      (Regex_primitive, [ Terminal Character ]);
      (Regex_primitive, [ Terminal Escape ]);
      ( Regex_primitive,
        [ Terminal Open_paren; NonTerminal Regex_union; Terminal Close_paren ]
      );
      ( Regex_primitive,
        [
          Terminal Open_bracket;
          NonTerminal Character_class;
          Terminal Close_bracket;
        ] );
      (Character_class, [ NonTerminal Character_class_entry ]);
      ( Character_class,
        [ NonTerminal Character_class_entry; NonTerminal Character_class ] );
      (Character_class_entry, [ Terminal Character ]);
      (Character_class_entry, [ Terminal Escape ]);
    ]

let rec regex_of_regex_syntax_tree
    (node : (regex_token_type, regex_rule) syntax_tree) : uchar regex =
  let expand_escape (value : string) : uchar =
    let escaped_char = value.[1] in
    (match escaped_char with
    | 'n' -> '\n'
    | 't' -> '\t'
    | 'r' -> '\r'
    | _ -> escaped_char)
    |> u
  in

  let flatten_character_class
      (node : (regex_token_type, regex_rule) syntax_tree) : uchar list =
    let extract_character (node : (regex_token_type, regex_rule) syntax_tree) :
        uchar =
      match node with
      | Node (Character_class_entry, [ Leaf { token_type = Character; value } ])
        ->
          u value.[0]
      | Node (Character_class_entry, [ Leaf { token_type = Escape; value } ]) ->
          expand_escape value
      | _ -> failwith "Not a member of a character class"
    in

    let rec flatten_character_class_into_rev
        (node : (regex_token_type, regex_rule) syntax_tree) (res : uchar list) :
        uchar list =
      match node with
      | Node (Character_class, [ entry; q ]) ->
          flatten_character_class_into_rev q (extract_character entry :: res)
      | Node (Character_class, [ entry ]) -> extract_character entry :: res
      | _ -> failwith "Not a character class"
    in
    List.rev (flatten_character_class_into_rev node [])
  in

  let build_character_class (c : uchar list) : uchar regex =
    let rec build_character_class_into (c : uchar list) (r : uchar regex) =
      match c with
      | [] -> r
      | a :: dash :: b :: q when dash = u '-' ->
          build_character_class_into q (add_character_range a b r)
      | a :: q -> build_character_class_into q (add_character a r)
    in
    build_character_class_into c Regex.Empty
  in

  match node with
  | Node (Regex_union, [ node ]) -> regex_of_regex_syntax_tree node
  | Node (Regex_union, [ node1; Leaf { token_type = Or }; node2 ]) ->
      Regex.Union
        (regex_of_regex_syntax_tree node1, regex_of_regex_syntax_tree node2)
  | Node (Regex_concatenation, [ node ]) -> regex_of_regex_syntax_tree node
  | Node (Regex_concatenation, [ node1; node2 ]) ->
      Regex.Concatenation
        (regex_of_regex_syntax_tree node1, regex_of_regex_syntax_tree node2)
  | Node (Regex_primitive, [ node; Leaf { token_type = Star } ]) ->
      Regex.Star (regex_of_regex_syntax_tree node)
  | Node (Regex_primitive, [ node; Leaf { token_type = Plus } ]) ->
      let inner = regex_of_regex_syntax_tree node in
      Regex.Concatenation (inner, Regex.Star inner)
  | Node (Regex_primitive, [ node; Leaf { token_type = Question } ]) ->
      Regex.Union (Regex.Epsilon, Regex.Star (regex_of_regex_syntax_tree node))
  | Node (Regex_primitive, [ Leaf { token_type = Character; value } ]) ->
      Regex.Symbol (u value.[0])
  | Node (Regex_primitive, [ Leaf { token_type = Escape; value } ]) ->
      Regex.Symbol (expand_escape value)
  | Node
      ( Regex_primitive,
        [
          Leaf { token_type = Open_paren };
          node;
          Leaf { token_type = Close_paren };
        ] ) ->
      regex_of_regex_syntax_tree node
  | Node
      ( Regex_primitive,
        [
          Leaf { token_type = Open_bracket };
          node;
          Leaf { token_type = Close_bracket };
        ] ) ->
      let character_class = flatten_character_class node in
      build_character_class character_class
  | _ -> failwith "Invalid rule"

let parse_regex (src : string) : uchar regex =
  let tokens = tokenize regex_token_rules Eof src in
  let automaton = construit_automate_LR1 regex_grammar Regex_union Eof in
  let tree = parse automaton Eof tokens Regex_union in
  regex_of_regex_syntax_tree tree
