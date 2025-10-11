open Regex
open Lexer
open Parser

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

let add_character (c : char) (r : char regex) : char regex =
  Regex.Union (r, Regex.Symbol c)

let rec add_character_range (start : char) (last : char) (r : char regex) =
  if start = last then add_character start r
  else
    add_character_range
      (char_of_int (int_of_char start + 1))
      last (add_character start r)

let regex_token_rules =
  [
    (Regex.Symbol '(', Open_paren);
    (Regex.Symbol ')', Close_paren);
    (Regex.Symbol '[', Open_bracket);
    (Regex.Symbol ']', Close_bracket);
    (Regex.Symbol '|', Or);
    (Regex.Symbol '*', Star);
    (Regex.Symbol '+', Plus);
    (Regex.Symbol '?', Question);
    ( Regex.Concatenation
        ( Regex.Symbol '\\',
          Regex.Empty |> add_character '(' |> add_character ')'
          |> add_character '|' |> add_character '*' |> add_character '\\'
          |> add_character 'n' |> add_character 't' |> add_character 'r'
          |> add_character '[' |> add_character ']' |> add_character '+'
          |> add_character '?' ),
      Escape );
    ( Regex.Empty
      |> add_character_range ' ' '\''
      (* (, ), * *)
      |> add_character_range '+' '{'
      (* | *)
      |> add_character_range '}' '~',
      Character );
  ]

type regex_rule = Regex | Character_class | Character_class_entry

let regex_grammar =
  [
    (Regex, [ Terminal Character ]);
    (Regex, [ Terminal Escape ]);
    (Regex, [ Terminal Open_paren; NonTerminal Regex; Terminal Close_paren ]);
    (Regex, [ NonTerminal Regex; Terminal Or; NonTerminal Regex ]);
    (Regex, [ NonTerminal Regex; Terminal Star ]);
    (Regex, [ NonTerminal Regex; Terminal Plus ]);
    (Regex, [ NonTerminal Regex; Terminal Question ]);
    (Regex, [ NonTerminal Regex; NonTerminal Regex ]);
    ( Regex,
      [
        Terminal Open_bracket;
        NonTerminal Character_class;
        Terminal Close_bracket;
      ] );
    ( Character_class,
      [ NonTerminal Character_class_entry; NonTerminal Character_class ] );
    (Character_class, [ NonTerminal Character_class_entry ]);
    (Character_class_entry, [ Terminal Character ]);
    (Character_class_entry, [ Terminal Escape ]);
  ]

let rec regex_of_regex_syntax_tree
    (node : (regex_token_type, regex_rule) syntax_tree) : char regex =
  let expand_escape (value : string) : char =
    let escaped_char = value.[1] in
    match escaped_char with
    | 'n' -> '\n'
    | 't' -> '\t'
    | 'r' -> '\r'
    | _ -> escaped_char
  in

  let flatten_character_class
      (node : (regex_token_type, regex_rule) syntax_tree) : char list =
    let extract_character (node : (regex_token_type, regex_rule) syntax_tree) :
        char =
      match node with
      | Node (Character_class_entry, [ Leaf { token_type = Character; value } ])
        ->
          value.[0]
      | Node (Character_class_entry, [ Leaf { token_type = Escape; value } ]) ->
          expand_escape value
      | _ -> failwith "Not a member of a character class"
    in

    let rec flatten_character_class_into_rev
        (node : (regex_token_type, regex_rule) syntax_tree) (res : char list) :
        char list =
      match node with
      | Node (Character_class, [ entry; q ]) ->
          flatten_character_class_into_rev q (extract_character entry :: res)
      | Node (Character_class, [ entry ]) -> extract_character entry :: res
      | _ -> failwith "Not a character class"
    in
    List.rev (flatten_character_class_into_rev node [])
  in

  let build_character_class (c : char list) : char regex =
    let rec build_character_class_into (c : char list) (r : char regex) =
      match c with
      | [] -> r
      | a :: '-' :: b :: q ->
          build_character_class_into q (add_character_range a b r)
      | a :: q -> build_character_class_into q (add_character a r)
    in
    build_character_class_into c Regex.Empty
  in

  match node with
  | Node (Regex, [ Leaf { token_type = Character; value } ]) ->
      Regex.Symbol value.[0]
  | Node (Regex, [ Leaf { token_type = Escape; value } ]) ->
      Regex.Symbol (expand_escape value)
  | Node
      ( Regex,
        [
          Leaf { token_type = Open_paren };
          inner;
          Leaf { token_type = Close_paren };
        ] ) ->
      regex_of_regex_syntax_tree inner
  | Node (Regex, [ left; Leaf { token_type = Or }; right ]) ->
      Regex.Union
        (regex_of_regex_syntax_tree left, regex_of_regex_syntax_tree right)
  | Node (Regex, [ inner; Leaf { token_type = Star } ]) ->
      Regex.Star (regex_of_regex_syntax_tree inner)
  | Node (Regex, [ inner; Leaf { token_type = Plus } ]) ->
      let inner_regex = regex_of_regex_syntax_tree inner in
      Regex.Concatenation (inner_regex, Regex.Star inner_regex)
  | Node (Regex, [ inner; Leaf { token_type = Question } ]) ->
      let inner_regex = regex_of_regex_syntax_tree inner in
      Regex.Union (Regex.Epsilon, inner_regex)
  | Node (Regex, [ first; second ]) ->
      Regex.Concatenation
        (regex_of_regex_syntax_tree first, regex_of_regex_syntax_tree second)
  | Node (Character_class, _) ->
      build_character_class (flatten_character_class node)
  | _ -> failwith "Invalid rule"

let parse_regex (src : string) : char regex =
  let tokens = tokenize regex_token_rules Eof src in
  let automaton = construit_automate_LR1 regex_grammar Regex Eof in
  let tree = parse automaton Eof tokens in
  regex_of_regex_syntax_tree tree
