open Lexer
open Regex
open Utils

type token_type = Or | Star | Open_Paren | Close_Paren | Epsilon | Symbol

let string_of_token_type (t : token_type) =
  match t with
  | Or -> "Or"
  | Star -> "Star"
  | Open_Paren -> "Open_Paren"
  | Close_Paren -> "Close_Paren"
  | Epsilon -> "Epsilon"
  | Symbol -> "Symbol"

let epsilon_regex =
  List.fold_left
    (fun acc c -> Concatenation (acc, Symbol c))
    Epsilon (explode "EPSILON")

let special_rules =
  [
    (Regex.Symbol '|', Or);
    (Regex.Symbol '*', Star);
    (Regex.Symbol '(', Open_Paren);
    (Regex.Symbol ')', Close_Paren);
    (Regex.Symbol ')', Close_Paren);
    (epsilon_regex, Epsilon);
  ]

let symbol_rules =
  explode "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"
  |> List.map (fun c -> (Regex.Symbol c, Symbol))

let regex_rules = special_rules @ symbol_rules
let text_regex_source = "abc|(123)*|EPSILON"
let tokens = tokenize regex_rules text_regex_source

let _ =
  List.fold_left
    (fun () token -> print_endline (string_of_token string_of_token_type token))
    () tokens
