open Regex
open Automaton

let r =
  Star
    (Concatenation
       ( Union (Concatenation (Symbol 'a', Star (Symbol 'b')), Epsilon),
         Star (Symbol 'c') ))

let epsilon_automaton = automaton_of_regex r

(* print_automaton
  (fun s -> match s with Epsilon -> "epsilon" | Symbol a -> String.make 1 a)
  string_of_int epsilon_automaton *)

let automaton = remove_epsilon_transitions epsilon_automaton

(* print_automaton (String.make 1) string_of_int automaton *)

let automaton_det = determinize automaton;;

print_automaton (String.make 1)
  (fun state ->
    List.fold_left
      (fun acc el ->
        acc ^ (if not (acc = "[") then ", " else "") ^ string_of_int el)
      "[" state
    ^ "]")
  automaton_det
