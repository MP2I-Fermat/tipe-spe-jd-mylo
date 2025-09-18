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
  let rec remove_transitons_from_states (remaining_states : 'state list)
      (final_states : 'state list)
      (transitions : ('state * 'symbol or_epsilon * 'state) list) =
    let non_epsilon_transitions =
      transitions
      |> List.filter_map (fun (state0, symbol, state1) ->
             match symbol with
             | Epsilon -> None
             | Symbol actual_symbol -> Some (state0, actual_symbol, state1))
    in
    match remaining_states with
    | [] ->
        {
          states = a.states;
          initial_states = a.initial_states;
          final_states;
          transitions = non_epsilon_transitions;
        }
    | state :: next_remaining_states ->
        let state_outgoing_transitions =
          transitions
          |> List.filter_map (fun (state0, symbol, state1) ->
                 if state0 = state && not (state1 = state && symbol = Epsilon)
                 then Some (symbol, state1)
                 else None)
        in

        let next_final_states =
          if List.mem state final_states then
            let new_final_states =
              a.states
              |> List.filter (fun other_state ->
                     List.mem (other_state, Epsilon, state) transitions)
              |> List.filter (fun state -> not (List.mem state final_states))
            in
            final_states @ new_final_states
          else final_states
        in

        let new_transitions =
          a.states
          |> List.map (fun other_state ->
                 if other_state = state then transitions
                 else if List.mem (other_state, Epsilon, state) transitions then
                   List.map
                     (fun (symbol, state1) -> (other_state, symbol, state1))
                     state_outgoing_transitions
                 else transitions)
          |> List.flatten
          |> List.filter (fun transition ->
                 not (List.mem transition transitions))
        in
        let next_transitions =
          transitions @ new_transitions
          |> List.filter (fun (_, symbol, state1) ->
                 not (state1 = state && symbol = Epsilon))
        in

        remove_transitons_from_states next_remaining_states next_final_states
          next_transitions
  in
  remove_transitons_from_states a.states a.final_states a.transitions

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
        process_remaining_states (new_states @ states)
          (new_states @ other_states)
          (new_transitions @ transitions)
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
