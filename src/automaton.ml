open Utils

type ('symbol, 'state) deterministic_automaton = {
  states : 'state Hashset.t;
  initial_state : 'state;
  final_states : 'state Hashset.t;
  transition : 'state -> 'symbol -> 'state option;
}

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
  automaton : ('symbol, 'state) deterministic_automaton;
  current_state : 'state;
}

let start_execution (a : ('symbol, 'state) deterministic_automaton) :
    ('symbol, 'state) execution_state =
  { automaton = a; current_state = a.initial_state }

let next_state (e : ('symbol, 'state) execution_state) (s : 'symbol) :
    ('symbol, 'state) execution_state option =
  let next_state = e.automaton.transition e.current_state s in
  match next_state with
  | None -> None
  | Some next_state ->
      Some { automaton = e.automaton; current_state = next_state }

let is_final_state (e : _ execution_state) : bool =
  Hashset.mem e.automaton.final_states e.current_state

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
                 if state1 = end_state && symbol = Epsilon then Some state0
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
    ('symbol, 'state list) deterministic_automaton =
  let initial_state = List.sort compare a.initial_states in
  let alphabet = Hashset.create () in
  List.iter (fun (_, s, _) -> Hashset.add alphabet s) a.transitions;

  (* multi_transitions[state0][symbol] is the set of all states reachable from state0 by reading symbol.
     This saves us iterating over all transitions for every super-state we create. *)
  let multi_transitions = Hashtbl.create 2 in

  (* Populate multi_transitions. *)
  List.iter
    (fun (state0, symbol, state1) ->
      let transitions_for_state0 =
        match Hashtbl.find_opt multi_transitions state0 with
        | None ->
            let t = Hashtbl.create 2 in
            Hashtbl.replace multi_transitions state0 t;
            t
        | Some t -> t
      in
      let transitions_for_symbol =
        match Hashtbl.find_opt transitions_for_state0 symbol with
        | None ->
            let t = Hashset.create () in
            Hashtbl.replace transitions_for_state0 symbol t;
            t
        | Some t -> t
      in
      Hashset.add transitions_for_symbol state1)
    a.transitions;

  (* transitions_for state0 is a dictionary d such that d[symbol] is the
     super-state reached by reading symbol from the super-state state0. *)
  let transitions_for (state : 'state list) : ('symbol, 'state list) Hashtbl.t =
    (* end_state_for_symbol symbol is the super-state reached by reading symbol from the super-state `state` *)
    let end_state_for_symbol (s : 'symbol) =
      state
      |> List.map (fun simple_state ->
             match Hashtbl.find_opt multi_transitions simple_state with
             | None -> []
             | Some transitions -> (
                 match Hashtbl.find_opt transitions s with
                 | None -> []
                 | Some s -> Hashset.to_list s))
      |> List.flatten |> List.sort_uniq compare
    in
    let res = Hashtbl.create 2 in
    Hashset.iter
      (fun s -> Hashtbl.replace res s (end_state_for_symbol s))
      alphabet;
    res
  in

  (* transitions[state0][symbol] is the super-state reached by reading symbol from the super-state state0. *)
  let transitions = Hashtbl.create 2 in
  (* A running collection of all super-states we have created. *)
  let states = Hashset.create () in
  (* Newly created super-states that have not yet been processed. *)
  let pending_states = Hashset.create () in

  Hashset.add pending_states initial_state;

  while not (Hashset.is_empty pending_states) do
    let current_state = Hashset.remove_one pending_states in
    Hashset.add states current_state;
    let current_transitions = transitions_for current_state in
    Hashtbl.replace transitions current_state current_transitions;
    Hashtbl.iter
      (fun _ end_state ->
        if not (Hashset.mem states end_state) then
          Hashset.add pending_states end_state)
      current_transitions
  done;

  (* Compute final states. *)
  let final_states = Hashset.create () in
  Hashset.iter
    (fun state ->
      if
        List.exists
          (fun simple_state -> List.mem simple_state a.final_states)
          state
      then Hashset.add final_states state)
    states;

  {
    initial_state;
    states;
    final_states;
    transition =
      (fun state0 symbol ->
        let state_transitions = Hashtbl.find transitions state0 in
        Hashtbl.find_opt state_transitions symbol);
  }

let remove_state (state : 'state)
    (a : ('symbol, 'state) deterministic_automaton) :
    ('symbol, 'state) deterministic_automaton =
  if a.initial_state = state then
    failwith "Cannot remove the initial state of an automaton";

  let filtered_states = Hashset.create () in
  Hashset.iter
    (fun s -> if s <> state then Hashset.add filtered_states s)
    a.states;

  let filtered_final_states = Hashset.create () in
  Hashset.iter
    (fun s -> if s <> state then Hashset.add filtered_final_states s)
    a.final_states;

  {
    states = filtered_states;
    initial_state = a.initial_state;
    final_states = filtered_final_states;
    transition =
      (fun state0 symbol ->
        match a.transition state0 symbol with
        | None -> None
        | Some state1 when state1 = state -> None
        | Some state1 -> Some state1);
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
