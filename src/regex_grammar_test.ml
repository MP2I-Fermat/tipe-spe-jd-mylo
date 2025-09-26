open Regex_grammar
open Regex
open Automaton

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
