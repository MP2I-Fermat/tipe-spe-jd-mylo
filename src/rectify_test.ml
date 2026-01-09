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

let rec get_name (p : pattern) : variable option =
  match p with
  | Ident n -> Some n
  | Underscore -> None
  | Parenthesised inner -> get_name inner
  | TypeCoercion { inner } -> get_name inner
  | Constant _ -> None
  | Record _ -> None
  | List _ -> None
  | Construction _ -> None
  | Concatenation _ -> None
  | Tuple _ -> None
  | Or _ -> None
  | As { name } -> Some name

let rectified =
  program
  |> List.map (fun phrase ->
         match phrase with
         | ValueDefinition { bindings; is_rec } -> (
             let k = ref 0 in
             let defined_functions =
               bindings
               |> List.filter_map (fun (binding : binding) ->
                      match binding with
                      | Variable _ -> None
                      | Function { name; parameters; body } ->
                          let body_lin, k' = linearize body !k in
                          k := k';
                          Some
                            ( name,
                              FunctionLiteral
                                {
                                  style = Fun;
                                  cases = [ (parameters, body_lin) ];
                                } ))
             in

             let new_name (n : string) = n ^ "_new" in

             match cloture_rectifiable defined_functions with
             (* TODO: Dig down? *)
             | None -> phrase
             | Some clot ->
                 ValueDefinition
                   {
                     is_rec;
                     bindings =
                       bindings
                       |> List.map (fun (binding : binding) ->
                              match binding with
                              | Variable _ -> [ binding ]
                              | Function { name; parameters; body } ->
                                  let linearized_body =
                                    match List.assoc name defined_functions with
                                    | FunctionLiteral
                                        { cases = [ (_, body_lin) ] } ->
                                        body_lin
                                    | _ ->
                                        failwith
                                          "Didn't find expected definition"
                                  in

                                  let new_fn =
                                    (Function
                                       {
                                         name = new_name name;
                                         parameters =
                                           parameters @ [ Ident "cont" ];
                                         body =
                                           delinearize
                                             (push_new_names
                                                (rectify linearized_body clot
                                                   "cont")
                                                clot "cont" new_name);
                                       }
                                      : Caml_light.binding)
                                  in

                                  let interceptor =
                                    (Function
                                       {
                                         name;
                                         parameters =
                                           List.init (List.length parameters)
                                             (fun i ->
                                               Ident ("arg" ^ string_of_int i));
                                         body =
                                           FunctionApplication
                                             {
                                               receiver =
                                                 Variable (new_name name);
                                               arguments =
                                                 List.init
                                                   (List.length parameters)
                                                   (fun i ->
                                                     (Variable
                                                        ("arg" ^ string_of_int i)
                                                       : Caml_light.expression))
                                                 @ [
                                                     Parenthesised
                                                       {
                                                         style = Parenthesis;
                                                         inner =
                                                           FunctionLiteral
                                                             {
                                                               style = Fun;
                                                               cases =
                                                                 [
                                                                   ( [
                                                                       Ident
                                                                         "res";
                                                                     ],
                                                                     Variable
                                                                       "res" );
                                                                 ];
                                                             };
                                                       };
                                                   ];
                                             };
                                       }
                                      : Caml_light.binding)
                                  in

                                  [ new_fn; interceptor ])
                       |> List.concat;
                   })
         | _ -> phrase)
;;

print_endline (string_of_ast rectified)
