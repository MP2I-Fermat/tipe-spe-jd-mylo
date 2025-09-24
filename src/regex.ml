open Automaton

type 'symbol regex =
  | Empty
  | Epsilon
  | Symbol of 'symbol
  | Concatenation of 'symbol regex * 'symbol regex
  | Union of 'symbol regex * 'symbol regex
  | Star of 'symbol regex

(** `automaton_of_regex r` returns an automaton with epsilon-transitions that
    recognizes the same language as `r` *)
let automaton_of_regex (r : 'symbol regex) : ('symbol, int) epsilon_automaton =
  let rec automaton_of_regex_with_context (r : 'symbol regex)
      (state_count : int) : ('symbol, int) epsilon_automaton * int =
    match r with
    | Empty ->
        ( {
            states = [];
            initial_states = [];
            final_states = [];
            transitions = [];
          },
          state_count )
    | Epsilon ->
        ( {
            states = [ state_count ];
            initial_states = [ state_count ];
            final_states = [ state_count ];
            transitions = [];
          },
          state_count + 1 )
    | Symbol s ->
        ( {
            states = [ state_count; state_count + 1 ];
            initial_states = [ state_count ];
            final_states = [ state_count + 1 ];
            transitions = [ (state_count, Automaton.Symbol s, state_count + 1) ];
          },
          state_count + 2 )
    | Concatenation (l, r) ->
        let left_automaton, state_count =
          automaton_of_regex_with_context l state_count
        in
        let right_automaton, state_count =
          automaton_of_regex_with_context r state_count
        in
        let cross_transitions =
          left_automaton.final_states
          |> List.map (fun left_final_state ->
                 right_automaton.initial_states
                 |> List.map (fun right_initial_state ->
                        ( left_final_state,
                          Automaton.Epsilon,
                          right_initial_state )))
          |> List.flatten
        in

        ( {
            states = left_automaton.states @ right_automaton.states;
            initial_states = left_automaton.initial_states;
            final_states = right_automaton.final_states;
            transitions =
              left_automaton.transitions @ right_automaton.transitions
              @ cross_transitions;
          },
          state_count )
    | Union (l, r) ->
        let left_automaton, state_count =
          automaton_of_regex_with_context l state_count
        in
        let right_automaton, state_count =
          automaton_of_regex_with_context r state_count
        in
        ( {
            states = left_automaton.states @ right_automaton.states;
            initial_states =
              left_automaton.initial_states @ right_automaton.initial_states;
            final_states =
              left_automaton.final_states @ right_automaton.final_states;
            transitions =
              left_automaton.transitions @ right_automaton.transitions;
          },
          state_count )
    | Star r' ->
        let inner_automaton, state_count =
          automaton_of_regex_with_context r' state_count
        in
        let loopback_transitions =
          inner_automaton.final_states
          |> List.map (fun final_state ->
                 inner_automaton.initial_states
                 |> List.map (fun initial_state ->
                        (final_state, Automaton.Epsilon, initial_state)))
          |> List.flatten
        in
        let epsilon_state = state_count in
        ( {
            states = epsilon_state :: inner_automaton.states;
            initial_states = epsilon_state :: inner_automaton.initial_states;
            final_states = epsilon_state :: inner_automaton.final_states;
            transitions = inner_automaton.transitions @ loopback_transitions;
          },
          state_count + 1 )
  in
  fst (automaton_of_regex_with_context r 0)
