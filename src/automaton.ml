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

(** Returns an execution of a starting in a's initial_state *)
let start_execution (a : ('symbol, 'state) deterministic_automaton) :
    ('symbol, 'state) execution_state =
  { automaton = a; current_state = a.initial_state }

(** Returns the state following e after reading s. Returns None if the automaton
    has no such state. *)
let next_state (e : ('symbol, 'state) execution_state) (s : 'symbol) :
    ('symbol, 'state) execution_state option =
  let next_state = e.automaton.transition e.current_state s in
  match next_state with
  | None -> None
  | Some next_state ->
      Some { automaton = e.automaton; current_state = next_state }

(** Returns true if e is a final state. *)
let is_final_state (e : _ execution_state) : bool =
  Hashset.mem e.automaton.final_states e.current_state

(** `remove_epsilon_transitions a` returns an automaton equivalent to a with all
    epsilon-transitions removed.

    The returned automaton may not be deterministic. *)
let remove_epsilon_transitions (a : ('symbol, 'state) epsilon_automaton) :
    ('symbol, 'state) automaton =
  let incoming_epsilon_transitions = Hashtbl.create 2 in
  let outgoing_epsilon_transitions = Hashtbl.create 2 in
  let result_transitions = Hashtbl.create 2 in
  let result_final_states = Hashset.create () in

  List.iter (Hashset.add result_final_states) a.final_states;
  List.iter
    (fun (state0, symbol, state1) ->
      match symbol with
      | Epsilon ->
          let incoming_states =
            match Hashtbl.find_opt incoming_epsilon_transitions state1 with
            | None ->
                let t = Hashset.create () in
                Hashtbl.add incoming_epsilon_transitions state1 t;
                t
            | Some t -> t
          in
          Hashset.add incoming_states state0;
          let outgoing_states =
            match Hashtbl.find_opt outgoing_epsilon_transitions state0 with
            | None ->
                let t = Hashset.create () in
                Hashtbl.add outgoing_epsilon_transitions state0 t;
                t
            | Some t -> t
          in
          Hashset.add outgoing_states state1
      | Symbol s ->
          let outgoing_transitions =
            match Hashtbl.find_opt result_transitions state0 with
            | None ->
                let t = Hashtbl.create 2 in
                Hashtbl.add result_transitions state0 t;
                t
            | Some t -> t
          in
          let transitions_for_symbol =
            match Hashtbl.find_opt outgoing_transitions s with
            | None ->
                let t = Hashset.create () in
                Hashtbl.add outgoing_transitions s t;
                t
            | Some t -> t
          in
          Hashset.add transitions_for_symbol state1)
    a.transitions;

  while Hashtbl.length incoming_epsilon_transitions > 0 do
    let state, incoming_states =
      hashtbl_remove_one incoming_epsilon_transitions
    in

    if List.mem state a.final_states then
      Hashset.iter (Hashset.add result_final_states) incoming_states;

    (* Remove outgoing transitions from start states. *)
    Hashset.iter
      (fun start_state ->
        let outgoing_transitions =
          Hashtbl.find outgoing_epsilon_transitions start_state
        in
        Hashset.remove outgoing_transitions state)
      incoming_states;

    (* Add transitions from all incoming states to reachable states, bypassing this state. *)
    (match Hashtbl.find_opt result_transitions state with
    | None -> ()
    | Some state_transitions ->
        Hashtbl.iter
          (fun symbol end_states ->
            Hashset.iter
              (fun start_state ->
                let start_state_transitions =
                  match Hashtbl.find_opt result_transitions start_state with
                  | None ->
                      let t = Hashtbl.create 2 in
                      Hashtbl.add result_transitions start_state t;
                      t
                  | Some t -> t
                in
                let transitions_for_symbol =
                  match Hashtbl.find_opt start_state_transitions symbol with
                  | None ->
                      let t = Hashset.create () in
                      Hashtbl.add start_state_transitions symbol t;
                      t
                  | Some t -> t
                in
                Hashset.iter (Hashset.add transitions_for_symbol) end_states)
              incoming_states)
          state_transitions);

    (* Add epsilon transitions from incoming states bypassing this state *)
    match Hashtbl.find_opt outgoing_epsilon_transitions state with
    | None -> ()
    | Some end_states ->
        (* Don't introduce e-loops. *)
        Hashset.remove end_states state;
        Hashset.iter
          (fun start_state ->
            let outgoing_transitions =
              Hashtbl.find outgoing_epsilon_transitions start_state
            in
            Hashset.iter (Hashset.add outgoing_transitions) end_states)
          incoming_states;
        Hashset.iter
          (fun end_state ->
            let incoming_transitions =
              Hashtbl.find incoming_epsilon_transitions end_state
            in
            Hashset.iter (Hashset.add incoming_transitions) incoming_states)
          end_states
  done;

  {
    states = a.states;
    initial_states = a.initial_states;
    final_states = Hashset.to_list result_final_states;
    transitions =
      Hashtbl.to_seq result_transitions
      |> List.of_seq
      |> List.map (fun (state0, transitions) ->
             Hashtbl.to_seq transitions |> List.of_seq
             |> List.map (fun (symbol, end_states) ->
                    (state0, symbol, end_states)))
      |> List.flatten
      |> List.map (fun (state0, symbol, end_states) ->
             Hashset.to_list end_states
             |> List.map (fun state1 -> (state0, symbol, state1)))
      |> List.flatten;
  }

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
            Hashtbl.add multi_transitions state0 t;
            t
        | Some t -> t
      in
      let transitions_for_symbol =
        match Hashtbl.find_opt transitions_for_state0 symbol with
        | None ->
            let t = Hashset.create () in
            Hashtbl.add transitions_for_state0 symbol t;
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
    Hashset.iter (fun s -> Hashtbl.add res s (end_state_for_symbol s)) alphabet;
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
    Hashtbl.add transitions current_state current_transitions;
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

(** Returns an automaton identical to a but with state and all transitions
    leading to state removed.

    This is primarily used to preemptively end executions of a if they get stuck
    in a sinkhole. *)
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
