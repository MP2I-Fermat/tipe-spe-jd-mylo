open Utils
open Parser
open Caml_light;;

match Parser.trouve_conflits caml_light_automaton with
| None -> ()
| Some state -> failwith "caml_light grammar has conflicts"

let test_source =
  let test_source_fp = open_in "../test.ml" in
  let test_source =
    really_input_string test_source_fp (in_channel_length test_source_fp)
  in
  close_in test_source_fp;
  test_source

let syntax_tree = parse_caml_light_syntax_tree test_source
let ast = ast_of_syntax_tree syntax_tree;;

print_endline (string_of_ast ast)
