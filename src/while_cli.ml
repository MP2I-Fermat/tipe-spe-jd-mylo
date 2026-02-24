open Caml_light
open While

let main () =
  let test_source =
    if Array.length Sys.argv <= 1 then
      failwith "Merci de donner un argument : le nom de fichier"
    else begin
      let test_source_fp = open_in Sys.argv.(1) in
      let test_source =
        really_input_string test_source_fp (in_channel_length test_source_fp)
      in
      close_in test_source_fp;
      test_source
    end
  in
  let program = parse_caml_light_ast test_source in
  whilify_program program |> string_of_ast


let () = print_endline (main ())

