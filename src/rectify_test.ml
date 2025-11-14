open Caml_light
open Rectify

let test_source =
  let test_source_fp = open_in "../test.ml" in
  let test_source =
    really_input_string test_source_fp (in_channel_length test_source_fp)
  in
  close_in test_source_fp;
  test_source

let program = parse_caml_light_ast test_source
let rectified = rectify_program program;;

print_endline (string_of_ast rectified)
