type ('symbol, 'state) deterministic_automaton = {
  states : 'state Hashset.t;
  initial_state : 'state;
  final_states : 'state Hashset.t;
  transition : 'state -> 'symbol -> 'state option;
}
