open Utils
open Parser
open Caml_light

let string_of_situation
    ((((n, rule), idx), sigma) : (string, string) lr1_situation) : string =
  let rule_chars =
    List.map (fun x -> match x with Terminal c | NonTerminal c -> c) rule
  in
  let rule_beginning = list_beginning rule_chars idx |> String.concat " " in
  let rule_end = list_skip rule_chars idx |> String.concat " " in
  let sigma_s = Hashset.to_list sigma |> String.concat ", " in
  n ^ " -> " ^ rule_beginning ^ "^" ^ rule_end ^ " ~ {" ^ sigma_s ^ "}"

let string_of_caml_automaton_state (s : (string, string) lr1_automaton_state) :
    string =
  let strings =
    Hashtbl.to_seq s |> List.of_seq |> List.map string_of_situation
  in
  String.concat "\n" strings
;;

match Parser.trouve_conflits caml_light_automaton with
| None -> ()
| Some state ->
    print_endline (string_of_caml_automaton_state state);
    failwith "caml_light grammar has conflicts"

let test_source =
  let test_source_fp = open_in "../test.ml" in
  let test_source =
    really_input_string test_source_fp (in_channel_length test_source_fp)
  in
  close_in test_source_fp;
  test_source

let test_tree = parse_caml_light_syntax_tree test_source;;

print_syntax_tree test_tree
  (fun x -> x)
  (fun x -> x.value ^ "(" ^ x.token_type ^ ")")
