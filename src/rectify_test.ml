open Caml_light
open Rectify

let test_source =
  let test_source_fp = open_in Sys.argv.(1) in
  let test_source =
    really_input_string test_source_fp (in_channel_length test_source_fp)
  in
  close_in test_source_fp;
  test_source

let program = parse_caml_light_ast test_source

let rectified =
  program
  |> List.map (fun phrase ->
         match phrase with
         | ValueDefinition { bindings; is_rec } ->
             ValueDefinition
               {
                 is_rec;
                 bindings =
                   bindings
                   |> List.map (fun (binding : binding) ->
                          match binding with
                          | Variable { lhs; value } ->
                              (Variable
                                 {
                                   lhs;
                                   value = delinearize (fst (linearize value 0));
                                 }
                                : binding)
                          | Function { name; parameters; body } ->
                              Function
                                {
                                  name;
                                  parameters;
                                  body = delinearize (fst (linearize body 0));
                                });
               }
         | Expression e -> Expression (delinearize (fst (linearize e 0)))
         | _ -> phrase)
;;

print_endline (string_of_ast rectified)
