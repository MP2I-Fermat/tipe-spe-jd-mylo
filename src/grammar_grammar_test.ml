open Grammar_grammar
open Parser
open Automaton
open Utils

let automaton = construit_automate_LR1 grammar_rules Grammar Eof

let string_of_grammar_node_type t =
  match t with
  | Grammar -> "G"
  | Grammar_entry -> "Ge"
  | Terminal_definition -> "T"
  | Rule_identifier_list -> "L"
  | Rule_identifier_list_entry -> "I"
  | NonTerminal_definition -> "NT"

let string_of_grammar_token_type t =
  match t with
  | Terminal_pattern -> "t"
  | Derivation_symbol -> "der"
  | Identifier -> "id"
  | Question -> "?"
  | Whitespace -> "<sp>"
  | Newline -> "\\n"
  | Comment_start -> "#"
  | Unrecognizable -> "?"
  | Eof -> "Eof"

let string_of_lr1_grammar_symbol s =
  match s with
  | Terminal t -> string_of_grammar_token_type t
  | NonTerminal t -> string_of_grammar_node_type t

let string_of_situation
    (((n, rule), idx, sigma) :
      (grammar_token_type, grammar_node_type) lr1_situation) : string =
  let ns = string_of_grammar_node_type n in
  let rule_strings = List.map string_of_lr1_grammar_symbol rule in
  let rule_beginning = String.concat " " (list_beginning rule_strings idx) in
  let rule_end = String.concat " " (list_skip rule_strings idx) in
  let sigma_s =
    List.map string_of_grammar_token_type sigma |> String.concat ", "
  in
  ns ^ " -> " ^ rule_beginning ^ "^" ^ rule_end ^ " ~ {" ^ sigma_s ^ "}"

let string_of_lr1_grammar_state
    (s : (grammar_token_type, grammar_node_type) lr1_automaton_state) : string =
  let strings = List.map string_of_situation s in
  "(" ^ String.concat ", " strings ^ ")"
;;

print_automaton string_of_lr1_grammar_symbol string_of_lr1_grammar_state
  automaton;

assert (trouve_conflits automaton = None)
