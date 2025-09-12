open Automaton

(* Example from the TD *)
let a : (char, int) epsilon_automaton =
  {
    states = [ 0; 1; 2; 3; 4; 5; 6 ];
    initial_states = [ 0 ];
    final_states = [ 5; 6 ];
    transitions =
      [
        (0, Epsilon, 1);
        (0, Symbol 'a', 4);
        (1, Symbol 'a', 2);
        (1, Symbol 'c', 4);
        (2, Symbol 'b', 3);
        (3, Epsilon, 6);
        (3, Symbol 'a', 5);
        (4, Epsilon, 5);
        (5, Symbol 'b', 5);
      ];
  }
;;

print_automaton
  (fun c -> match c with Epsilon -> "epsilon" | Symbol s -> String.make 1 s)
  string_of_int a

let a_simpl = remove_epsilon_transitions a;;

print_automaton (String.make 1) string_of_int a_simpl

let a_det = determinize a_simpl;;

print_automaton (String.make 1)
  (fun state ->
    List.fold_left
      (fun acc el ->
        acc ^ (if not (acc = "[") then ", " else "") ^ string_of_int el)
      "[" state
    ^ "]")
  a_det
