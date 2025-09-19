open Lexer

type ('token_type, 'non_terminal) grammar_entry =
  | NonTerminal of 'non_terminal
  | Terminal of 'token_type

type ('token_type, 'non_terminal) grammar =
  'non_terminal * ('token_type, 'non_terminal) grammar_entry list

type ('token_type, 'non_terminal) syntax_tree =
  | Node of 'non_terminal * ('token_type, 'non_terminal) syntax_tree list
  | Leaf of 'token_type token

let parse (g : ('token_type, 'non_terminal) grammar)
    (text : 'token_type token list) : ('token_type, 'non_terminal) syntax_tree =
  _
