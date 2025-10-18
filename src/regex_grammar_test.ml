open Regex_grammar
open Regex
open Automaton
open Parser
open Utils

let r2 =
  Regex.Star
    (Regex.Concatenation
       ( Regex.Epsilon |> add_character_range ' ' '~',
         Regex.Epsilon |> add_character_range ' ' '~' ))

(* let _ =
  print_endline "Starting...";
  let epsilon_automaton = automaton_of_regex r2 in
  print_endline "Made automaton";
  let automaton = remove_epsilon_transitions epsilon_automaton in
  print_endline "Removed e-transitions";
  let determinized = determinize automaton in
  print_endline "Determinized";
  let _ = remove_state [] determinized in
  print_endline "Done!" *)

let automaton = construit_automate_LR1 regex_grammar Regex Eof

let string_of_regex_token_type (t : regex_token_type) =
  match t with
  | Character -> "<c>"
  | Close_bracket -> "]"
  | Close_paren -> ")"
  | Eof -> "<eof>"
  | Escape -> "<esc>"
  | Open_bracket -> "["
  | Open_paren -> "("
  | Or -> "|"
  | Plus -> "+"
  | Question -> "?"
  | Star -> "*"

let string_of_regex_rule (r : regex_rule) =
  match r with
  | Regex -> "R"
  | Character_class -> "CC"
  | Character_class_entry -> "CCE"

let string_of_regex_grammar_entry
    (e : (regex_token_type, regex_rule) grammar_entry) =
  match e with
  | NonTerminal r -> string_of_regex_rule r
  | Terminal t -> string_of_regex_token_type t

let string_of_regex_situation
    (((n, rule), idx, sigma) : (regex_token_type, regex_rule) lr1_situation) :
    string =
  let ns = string_of_regex_rule n in
  let rule_beginning =
    list_beginning rule idx
    |> List.map string_of_regex_grammar_entry
    |> String.concat " "
  in
  let rule_end =
    list_skip rule idx
    |> List.map string_of_regex_grammar_entry
    |> String.concat " "
  in
  let sigma_s =
    List.map string_of_regex_token_type sigma |> String.concat ", "
  in
  ns ^ " -> " ^ rule_beginning ^ "^" ^ rule_end ^ " ~ {" ^ sigma_s ^ "}"

let string_of_regex_state
    (s : (regex_token_type, regex_rule) lr1_automaton_state) : string =
  let strings = List.map string_of_regex_situation s in
  "(" ^ String.concat ", " strings ^ ")"
;;

(* print_automaton string_of_regex_grammar_entry string_of_regex_state automaton;; *)

match trouve_conflits automaton with
| None -> ()
| Some state ->
    print_endline (string_of_regex_state state);
    assert false

let r1 = parse_regex "abc|(bc)*"

let _ =
  assert (
    r1
    = Regex.Concatenation
        ( Regex.Symbol 'a',
          Regex.Concatenation
            ( Regex.Symbol 'b',
              Regex.Union
                ( Regex.Symbol 'c',
                  Regex.Star
                    (Regex.Concatenation (Regex.Symbol 'b', Regex.Symbol 'c'))
                ) ) ))
