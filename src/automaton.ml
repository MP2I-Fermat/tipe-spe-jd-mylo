type ('symbol, 'state) automaton = {
  states : 'state list;
  initial_states : 'state list;
  final_states : 'state list;
  transitions : ('state * 'symbol * 'state) list;
}

type 'symbol or_epsilon = Epsilon | Symbol of 'symbol

type ('symbol, 'state) epsilon_automaton =
  ('symbol or_epsilon, 'state) automaton

type ('symbol, 'state) execution_state = {
  automaton : ('symbol, 'state) automaton;
  current_state : 'state;
}

exception Not_deterministic

let start_execution (a : ('symbol, 'state) automaton) :
    ('symbol, 'state) execution_state =
  match a.initial_states with
  | initial_state :: [] -> { automaton = a; current_state = initial_state }
  | _ -> raise Not_deterministic

let next_state (e : ('symbol, 'state) execution_state) (s : 'symbol) :
    ('symbol, 'state) execution_state option =
  match
    List.find_all
      (fun (state0, symbol, state1) -> state0 = e.current_state && symbol = s)
      e.automaton.transitions
  with
  | [] -> None
  | (_, _, state1) :: [] ->
      Some { automaton = e.automaton; current_state = state1 }
  | _ -> raise Not_deterministic

let is_final_state (e : _ execution_state) : bool =
  List.mem e.current_state e.automaton.final_states

(** `remove_epsilon_transitions a` returns an automaton equivalent to a with all
    epsilon-transitions removed.

    The returned automaton may not be deterministic. *)
let remove_epsilon_transitions (a : ('symbol, 'state) epsilon_automaton) :
    ('symbol, 'state) automaton =
  let rec build_result_from
      (remaining_epsilon_transitions : ('state list * 'state) list)
      (result_transitions : ('state * 'symbol * 'state) list)
      (result_final_states : 'state list) =
    match remaining_epsilon_transitions with
    | [] ->
        {
          states = a.states;
          initial_states = a.initial_states;
          final_states = result_final_states;
          transitions = result_transitions;
        }
    | (incoming_states, end_state) :: remaining_epsilon_transitions ->
        let next_final_states =
          if List.mem end_state result_final_states then
            let new_final_states =
              List.filter
                (fun state -> not (List.mem state result_final_states))
                incoming_states
            in
            List.rev_append new_final_states result_final_states
          else result_final_states
        in

        let outgoing_transitions =
          List.filter_map
            (fun (state0, symbol, state1) ->
              if state0 = end_state then Some (symbol, state1) else None)
            result_transitions
        in
        let new_transitions =
          incoming_states
          |> List.map (fun state0 ->
                 List.map
                   (fun (symbol, state1) -> (state0, symbol, state1))
                   outgoing_transitions)
          |> List.flatten
          |> List.filter (fun new_transition ->
                 not (List.mem new_transition result_transitions))
        in
        let next_transitions =
          List.rev_append new_transitions result_transitions
        in

        let outgoing_epsilon_transitions =
          List.filter_map
            (fun (incoming_states', end_state') ->
              if List.mem end_state incoming_states' then Some end_state'
              else None)
            remaining_epsilon_transitions
        in
        let new_epsilon_transitions =
          incoming_states
          |> List.map (fun state0 ->
                 List.map
                   (fun state1 -> (state0, state1))
                   outgoing_epsilon_transitions)
          |> List.flatten
          (* Don't introduce any e-loops. *)
          |> List.filter (fun (state0, state1) -> state0 <> state1)
        in
        let next_remaining_epsilon_transitions =
          List.map
            (fun (incoming_states, end_state) ->
              let new_incoming_states =
                new_epsilon_transitions
                |> List.filter_map (fun (state0, state1) ->
                       if state1 = end_state then Some state0 else None)
                |> List.filter (fun new_incoming_state ->
                       not (List.mem new_incoming_state incoming_states))
              in
              (List.rev_append new_incoming_states incoming_states, end_state))
            remaining_epsilon_transitions
        in

        build_result_from next_remaining_epsilon_transitions next_transitions
          next_final_states
  in
  let epsilon_transitions =
    a.states
    |> List.map (fun end_state ->
           ( List.filter_map
               (fun (state0, symbol, state1) ->
                 if state1 = end_state && symbol = Epsilon then Some state1
                 else None)
               a.transitions,
             end_state ))
    |> List.filter (fun (start_states, _) -> not (start_states = []))
  in
  let non_epsilon_transitions =
    List.filter_map
      (fun (state0, symbol, state1) ->
        match symbol with
        | Epsilon -> None
        | Symbol actual_symbol -> Some (state0, actual_symbol, state1))
      a.transitions
  in
  build_result_from epsilon_transitions non_epsilon_transitions a.final_states

(** `determinize a` returns an automaton equivalent to `a` that is deterministic
    and complete. *)
let determinize (a : ('symbol, 'state) automaton) :
    ('symbol, 'state list) automaton =
  let initial_state = List.sort compare a.initial_states in
  let alphabet =
    a.transitions
    |> List.map (fun (_, symbol, _) -> symbol)
    |> List.sort_uniq compare
  in
  let transitions_for (state : 'state list) =
    let transition_for_symbol (s : 'symbol) =
      let end_state =
        state
        |> List.map (fun simple_state ->
               List.filter
                 (fun (state0, symbol, state1) ->
                   state0 = simple_state && symbol = s)
                 a.transitions)
        |> List.flatten
        |> List.map (fun (_, _, state1) -> state1)
        |> List.sort_uniq compare
      in
      (state, s, end_state)
    in
    List.map transition_for_symbol alphabet
  in
  let rec process_remaining_states (states : 'state list list)
      (remaining_states : 'state list list)
      (transitions : ('state list * 'symbol * 'state list) list) =
    match remaining_states with
    | [] ->
        {
          states;
          initial_states = [ initial_state ];
          final_states =
            List.filter
              (fun state ->
                List.find_opt
                  (fun simple_state -> List.mem simple_state a.final_states)
                  state
                != None)
              states;
          transitions;
        }
    | state :: other_states ->
        let new_transitions = transitions_for state in
        let new_states =
          new_transitions
          |> List.map (fun (_, _, state1) -> state1)
          |> List.filter (fun state -> not (List.mem state states))
          |> List.sort_uniq compare
        in
        process_remaining_states
          (List.rev_append new_states states)
          (List.rev_append new_states other_states)
          (List.rev_append new_transitions transitions)
  in
  process_remaining_states [ initial_state ] [ initial_state ] []

let remove_state (state : 'state) (a : ('symbol, 'state) automaton) :
    ('symbol, 'state) automaton =
  {
    states = List.filter (fun s -> not (s = state)) a.states;
    initial_states = List.filter (fun s -> not (s = state)) a.initial_states;
    final_states = List.filter (fun s -> not (s = state)) a.final_states;
    transitions =
      List.filter
        (fun (state0, _, state1) -> not (state0 = state || state1 = state))
        a.transitions;
  }

let print_automaton (string_of_symbol : 'symbol -> string)
    (string_of_state : 'state -> string) (a : ('symbol, 'state) automaton) :
    unit =
  print_endline "Automaton:";
  print_endline "Initial states:";
  List.fold_left
    (fun () state -> print_endline ("- " ^ string_of_state state))
    () a.initial_states;
  print_endline "Final states:";
  List.fold_left
    (fun () state -> print_endline ("- " ^ string_of_state state))
    () a.final_states;
  print_endline "Transitions:";
  List.fold_left
    (fun () (state0, symbol, state1) ->
      print_endline
        ("- " ^ string_of_state state0 ^ " -- " ^ string_of_symbol symbol
       ^ " -> " ^ string_of_state state1))
    () a.transitions
