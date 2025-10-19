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

let automaton = construit_automate_LR1 regex_grammar Regex_union Eof

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
  | Regex_union -> "Ru"
  | Regex_concatenation -> "Rc"
  | Regex_primitive -> "Rp"
  | Character_class -> "CC"
  | Character_class_entry -> "CCE"

let string_of_regex_grammar_entry
    (e : (regex_token_type, regex_rule) grammar_entry) =
  match e with
  | NonTerminal r -> string_of_regex_rule r
  | Terminal t -> string_of_regex_token_type t

let string_of_regex_situation
    ((((n, rule), idx), sigma) :
      (regex_token_type, regex_rule) lr0_situation * regex_token_type Hashset.t)
    : string =
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
    Hashset.to_list sigma
    |> List.map string_of_regex_token_type
    |> String.concat ", "
  in
  ns ^ " -> " ^ rule_beginning ^ "^" ^ rule_end ^ " ~ {" ^ sigma_s ^ "}"

let string_of_regex_state
    (s : (regex_token_type, regex_rule) lr1_automaton_state) : string =
  let strings =
    Hashtbl.to_seq s |> List.of_seq |> List.map string_of_regex_situation
  in
  "(" ^ String.concat ", " strings ^ ")"
;;

match trouve_conflits automaton with
| None -> ()
| Some state ->
    print_endline (string_of_regex_state state);
    assert false

let r1 =
  parse_regex "(abc|(de*f?|gh+))\\n([a-zA-Z0-9]+foooooooooooooooooooooooo\\()"

let _ =
  assert (
    r1
    = Regex.Concatenation
        ( Regex.Union
            ( Regex.Concatenation
                ( Regex.Symbol 'a',
                  Regex.Concatenation (Regex.Symbol 'b', Regex.Symbol 'c') ),
              Regex.Union
                ( Regex.Concatenation
                    ( Regex.Symbol 'd',
                      Regex.Concatenation
                        ( Regex.Star (Regex.Symbol 'e'),
                          Regex.Union
                            (Regex.Epsilon, Regex.Star (Regex.Symbol 'f')) ) ),
                  Regex.Concatenation
                    ( Regex.Symbol 'g',
                      Regex.Concatenation
                        (Regex.Symbol 'h', Regex.Star (Regex.Symbol 'h')) ) ) ),
          Regex.Concatenation
            ( Regex.Symbol '\n',
              Regex.Concatenation
                ( Regex.Concatenation
                    ( Regex.Union
                        ( Regex.Union
                            ( Regex.Union
                                ( Regex.Union
                                    ( Regex.Union
                                        ( Regex.Union
                                            ( Regex.Union
                                                ( Regex.Union
                                                    ( Regex.Union
                                                        ( Regex.Union
                                                            ( Regex.Union
                                                                ( Regex.Union
                                                                    ( Regex.Union
                                                                        ( Regex
                                                                          .Union
                                                                            ( Regex
                                                                              .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Empty,
                                                                                Regex
                                                                                .Symbol
                                                                                'a'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'b'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'c'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'd'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'e'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'f'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'g'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'h'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'i'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'j'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'k'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'l'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'm'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'n'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'o'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'p'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'q'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'r'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                's'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                't'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'u'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'v'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'w'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'x'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'y'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'z'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'A'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'B'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'C'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'D'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'E'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'F'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'G'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'H'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'I'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'J'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'K'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'L'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'M'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'N'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'O'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'P'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'Q'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'R'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'S'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'T'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'U'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'V'
                                                                                ),
                                                                              Regex
                                                                              .Symbol
                                                                                'W'
                                                                            ),
                                                                          Regex
                                                                          .Symbol
                                                                            'X'
                                                                        ),
                                                                      Regex
                                                                      .Symbol
                                                                        'Y' ),
                                                                  Regex.Symbol
                                                                    'Z' ),
                                                              Regex.Symbol '0'
                                                            ),
                                                          Regex.Symbol '1' ),
                                                      Regex.Symbol '2' ),
                                                  Regex.Symbol '3' ),
                                              Regex.Symbol '4' ),
                                          Regex.Symbol '5' ),
                                      Regex.Symbol '6' ),
                                  Regex.Symbol '7' ),
                              Regex.Symbol '8' ),
                          Regex.Symbol '9' ),
                      Regex.Star
                        (Regex.Union
                           ( Regex.Union
                               ( Regex.Union
                                   ( Regex.Union
                                       ( Regex.Union
                                           ( Regex.Union
                                               ( Regex.Union
                                                   ( Regex.Union
                                                       ( Regex.Union
                                                           ( Regex.Union
                                                               ( Regex.Union
                                                                   ( Regex.Union
                                                                       ( Regex
                                                                         .Union
                                                                           ( Regex
                                                                             .Union
                                                                               ( 
                                                                               Regex
                                                                               .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Union
                                                                                ( 
                                                                                Regex
                                                                                .Empty,
                                                                                Regex
                                                                                .Symbol
                                                                                'a'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'b'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'c'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'd'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'e'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'f'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'g'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'h'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'i'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'j'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'k'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'l'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'm'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'n'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'o'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'p'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'q'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'r'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                's'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                't'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'u'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'v'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'w'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'x'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'y'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'z'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'A'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'B'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'C'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'D'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'E'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'F'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'G'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'H'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'I'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'J'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'K'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'L'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'M'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'N'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'O'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'P'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'Q'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'R'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'S'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'T'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'U'
                                                                                ),
                                                                                Regex
                                                                                .Symbol
                                                                                'V'
                                                                                ),
                                                                               Regex
                                                                               .Symbol
                                                                                'W'
                                                                               ),
                                                                             Regex
                                                                             .Symbol
                                                                               'X'
                                                                           ),
                                                                         Regex
                                                                         .Symbol
                                                                           'Y'
                                                                       ),
                                                                     Regex
                                                                     .Symbol
                                                                       'Z' ),
                                                                 Regex.Symbol
                                                                   '0' ),
                                                             Regex.Symbol '1' ),
                                                         Regex.Symbol '2' ),
                                                     Regex.Symbol '3' ),
                                                 Regex.Symbol '4' ),
                                             Regex.Symbol '5' ),
                                         Regex.Symbol '6' ),
                                     Regex.Symbol '7' ),
                                 Regex.Symbol '8' ),
                             Regex.Symbol '9' )) ),
                  Regex.Concatenation
                    ( Regex.Symbol 'f',
                      Regex.Concatenation
                        ( Regex.Symbol 'o',
                          Regex.Concatenation
                            ( Regex.Symbol 'o',
                              Regex.Concatenation
                                ( Regex.Symbol 'o',
                                  Regex.Concatenation
                                    ( Regex.Symbol 'o',
                                      Regex.Concatenation
                                        ( Regex.Symbol 'o',
                                          Regex.Concatenation
                                            ( Regex.Symbol 'o',
                                              Regex.Concatenation
                                                ( Regex.Symbol 'o',
                                                  Regex.Concatenation
                                                    ( Regex.Symbol 'o',
                                                      Regex.Concatenation
                                                        ( Regex.Symbol 'o',
                                                          Regex.Concatenation
                                                            ( Regex.Symbol 'o',
                                                              Regex
                                                              .Concatenation
                                                                ( Regex.Symbol
                                                                    'o',
                                                                  Regex
                                                                  .Concatenation
                                                                    ( Regex
                                                                      .Symbol
                                                                        'o',
                                                                      Regex
                                                                      .Concatenation
                                                                        ( Regex
                                                                          .Symbol
                                                                            'o',
                                                                          Regex
                                                                          .Concatenation
                                                                            ( Regex
                                                                              .Symbol
                                                                                'o',
                                                                              Regex
                                                                              .Concatenation
                                                                                ( 
                                                                                Regex
                                                                                .Symbol
                                                                                'o',
                                                                                Regex
                                                                                .Concatenation
                                                                                ( 
                                                                                Regex
                                                                                .Symbol
                                                                                'o',
                                                                                Regex
                                                                                .Concatenation
                                                                                ( 
                                                                                Regex
                                                                                .Symbol
                                                                                'o',
                                                                                Regex
                                                                                .Concatenation
                                                                                ( 
                                                                                Regex
                                                                                .Symbol
                                                                                'o',
                                                                                Regex
                                                                                .Concatenation
                                                                                ( 
                                                                                Regex
                                                                                .Symbol
                                                                                'o',
                                                                                Regex
                                                                                .Concatenation
                                                                                ( 
                                                                                Regex
                                                                                .Symbol
                                                                                'o',
                                                                                Regex
                                                                                .Concatenation
                                                                                ( 
                                                                                Regex
                                                                                .Symbol
                                                                                'o',
                                                                                Regex
                                                                                .Concatenation
                                                                                ( 
                                                                                Regex
                                                                                .Symbol
                                                                                'o',
                                                                                Regex
                                                                                .Concatenation
                                                                                ( 
                                                                                Regex
                                                                                .Symbol
                                                                                'o',
                                                                                Regex
                                                                                .Concatenation
                                                                                ( 
                                                                                Regex
                                                                                .Symbol
                                                                                'o',
                                                                                Regex
                                                                                .Symbol
                                                                                '('
                                                                                )
                                                                                )
                                                                                )
                                                                                )
                                                                                )
                                                                                )
                                                                                )
                                                                                )
                                                                                )
                                                                                )
                                                                            ) )
                                                                    ) ) ) ) ) )
                                            ) ) ) ) ) ) ) ) ) ))
