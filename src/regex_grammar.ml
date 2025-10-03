open Regex
open Lexer
open Parser

type regex_token_type =
  | Open_paren
  | Close_paren
  | Or
  | Star
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
    (Regex.Symbol '|', Or);
    (Regex.Symbol '*', Star);
    ( Regex.Concatenation
        ( Regex.Symbol '\\',
          Regex.Empty |> add_character '(' |> add_character ')'
          |> add_character '|' |> add_character '*' |> add_character '\\'
          |> add_character 'n' |> add_character 't' |> add_character 'r' ),
      Escape );
    ( Regex.Empty
      |> add_character_range ' ' '\''
      (* (, ), * *)
      |> add_character_range '+' '{'
      (* | *)
      |> add_character_range '}' '~',
      Character );
  ]

type regex_rule = Regex

let regex_grammar =
  [
    (Regex, [ Terminal Character ]);
    (Regex, [ Terminal Escape ]);
    (Regex, [ Terminal Open_paren; NonTerminal Regex; Terminal Close_paren ]);
    (Regex, [ NonTerminal Regex; Terminal Or; NonTerminal Regex ]);
    (Regex, [ NonTerminal Regex; Terminal Star ]);
    (Regex, [ NonTerminal Regex; NonTerminal Regex ]);
  ]

let rec regex_of_regex_syntax_tree
    (t : (regex_token_type, regex_rule) syntax_tree) : char regex =
  match t with
  | Node (_, [ Leaf { token_type = Character; value } ]) ->
      Regex.Symbol value.[0]
  | Node (_, [ Leaf { token_type = Escape; value } ]) -> (
      let escaped_char = value.[1] in
      match escaped_char with
      | 'n' -> Regex.Symbol '\n'
      | 't' -> Regex.Symbol '\t'
      | 'r' -> Regex.Symbol '\r'
      | _ -> Regex.Symbol escaped_char)
  | Node
      ( _,
        [
          Leaf { token_type = Open_paren };
          inner;
          Leaf { token_type = Close_paren };
        ] ) ->
      regex_of_regex_syntax_tree inner
  | Node (_, [ left; Leaf { token_type = Or }; right ]) ->
      Regex.Union
        (regex_of_regex_syntax_tree left, regex_of_regex_syntax_tree right)
  | Node (_, [ inner; Leaf { token_type = Star } ]) ->
      Regex.Star (regex_of_regex_syntax_tree inner)
  | Node (_, [ first; second ]) ->
      Regex.Concatenation
        (regex_of_regex_syntax_tree first, regex_of_regex_syntax_tree second)
  | _ -> failwith "Invalid rule"

let parse_regex (src : string) : char regex =
  let tokens = tokenize regex_token_rules Eof src in
  let tree = parse regex_grammar tokens in
  regex_of_regex_syntax_tree tree
