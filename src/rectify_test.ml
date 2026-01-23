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
             let initial_functions =
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

             let new_name (n : string) = n ^ "_rectified" in

             match cloture_rectifiable initial_functions with
             (* TODO: Dig down? *)
             | None -> phrase
             | Some clot ->
                 let rectified_functions =
                   initial_functions
                   |> List.map (fun (name, definition) ->
                          let parameters, linearized_body =
                            match definition with
                            | FunctionLiteral { cases = [ case ] } -> case
                            | _ -> failwith "Bad state"
                          in

                          let rectified_body = rectify linearized_body clot in
                          let redefined_body =
                            push_rectified_definitions rectified_body clot
                              new_name
                          in

                          ( new_name name,
                            FunctionLiteral
                              {
                                style = Fun;
                                cases =
                                  [
                                    ( parameters @ [ Ident "cont" ],
                                      redefined_body );
                                  ];
                              } ))
                 in

                 let new_clot = List.map new_name clot in

                 let accumulator_functions, initial_constant =
                   match find_continuations rectified_functions clot with
                   | None -> (rectified_functions, None)
                   | Some continuations -> (
                       let extracted_continuations =
                         List.fold_left
                           (fun acc continuation ->
                             match acc with
                             | None -> None
                             | Some acc -> (
                                 match extract_continuation continuation with
                                 | None -> None
                                 | Some extracted_continuation ->
                                     Some (extracted_continuation :: acc)))
                           (Some []) continuations
                       in
                       match extracted_continuations with
                       | None -> (rectified_functions, None)
                       | Some extracted_continuations -> (
                           let initial = find_initials rectified_functions in
                           match initial with
                           | None -> (rectified_functions, None)
                           | Some (variables, initial) ->
                               if
                                 commutes extracted_continuations
                                 && List.length initial == 1
                               then
                                 ( rectified_functions
                                   |> List.map (fun (name, body) ->
                                          replace_continuations_with_accumulator
                                            [ (name, body) ]
                                            new_clot variables
                                          |> List.hd),
                                   Some (List.hd initial) )
                               else (rectified_functions, None)))
                 in

                 (* rmq: clot can only contain functions defined in defined_functions & their bodies *)
                 ValueDefinition
                   {
                     is_rec;
                     bindings =
                       bindings
                       |> List.map (fun (binding : binding) ->
                              match binding with
                              | Variable _ -> [ binding ]
                              | Function { name; parameters; body } ->
                                  let redefined =
                                    match
                                      List.assoc (new_name name)
                                        accumulator_functions
                                    with
                                    | FunctionLiteral f -> f
                                    | _ ->
                                        failwith
                                          "Unable to find redefined definition"
                                  in

                                  let new_parameters, new_body =
                                    match redefined.cases with
                                    | [ c ] -> c
                                    | _ -> failwith "Bad function"
                                  in

                                  let new_fn =
                                    (Function
                                       {
                                         name = new_name name;
                                         parameters = new_parameters;
                                         body = fst (delinearize new_body []);
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
                                                           (match
                                                              initial_constant
                                                            with
                                                           | None ->
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
                                                                           "res"
                                                                       );
                                                                     ];
                                                                 }
                                                           | Some cst ->
                                                               Constant cst);
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
