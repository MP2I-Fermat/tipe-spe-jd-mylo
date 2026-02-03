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

             (* Step 1: Linearize *)
             let linearized_functions =
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

             (* Step 2: Calculate rectifying set *)
             match cloture_rectifiable linearized_functions with
             (* TODO: Dig down? *)
             | None -> phrase
             | Some cloture_rect ->
                 (* Step 3: Rectify *)
                 let rectified_functions =
                   rectify linearized_functions cloture_rect
                 in

                 (* Step 4: Replace continuations with accumulators (if possible) *)
                 let accumulator_functions, initial_accumulator_constant =
                   (* Step 4a: Extract all continuations *)
                   match
                     find_continuations rectified_functions cloture_rect
                   with
                   | None -> (rectified_functions, None)
                   | Some continuations -> (
                       (* Step 4b: Extract composition with previous continuation form each continuation *)
                       let extracted_continuations =
                         continuations
                         |> List.filter_map extract_continuation_composition
                       in

                       if
                         List.length extracted_continuations
                         <> List.length continuations
                       then (rectified_functions, None)
                       else
                         (* Step 4c: Find the initial constant to use *)
                         let initial_constant =
                           find_initials rectified_functions
                         in
                         match initial_constant with
                         | None -> (rectified_functions, None)
                         | Some (variables, initial) ->
                             (* Step 4d: Check continuations can commute *)
                             if
                               commutes extracted_continuations
                               && List.length initial == 1
                             then
                               ( rectified_functions
                                 |> List.map (fun (name, body) ->
                                        replace_continuations_with_accumulator
                                          [ (name, body) ]
                                          cloture_rect variables
                                        |> List.hd),
                                 Some (List.hd initial) )
                             else (rectified_functions, None))
                 in

                 (* Step 5: Rename updated functions *)
                 let new_name (n : string) = n ^ "_rectified" in

                 let renamed_functions =
                   rename_elements accumulator_functions cloture_rect new_name
                 in

                 ValueDefinition
                   {
                     is_rec;
                     bindings =
                       bindings
                       |> List.map (fun (binding : binding) ->
                              match binding with
                              | Variable _ -> [ binding ]
                              | Function { name; parameters; body } ->
                                  let new_linearized_definition =
                                    match
                                      List.assoc (new_name name)
                                        renamed_functions
                                    with
                                    | FunctionLiteral f -> f
                                    | _ ->
                                        failwith
                                          "Unable to find redefined definition"
                                  in

                                  let new_parameters, new_linearized_body =
                                    match new_linearized_definition.cases with
                                    | [ c ] -> c
                                    | _ -> failwith "Bad function"
                                  in

                                  let new_definition =
                                    (Function
                                       {
                                         name = new_name name;
                                         parameters = new_parameters;
                                         body =
                                           fst
                                             (delinearize new_linearized_body []);
                                       }
                                      : Caml_light.binding)
                                  in

                                  let interceptor_parameter_names =
                                    parameters
                                    |> List.mapi (fun i parameter ->
                                           match get_name parameter with
                                           | Some name -> name
                                           | None -> "arg" ^ string_of_int i)
                                  in

                                  let interceptor =
                                    (Function
                                       {
                                         name;
                                         parameters =
                                           interceptor_parameter_names
                                           |> List.map (fun x -> Ident x);
                                         body =
                                           FunctionApplication
                                             {
                                               receiver =
                                                 Variable (new_name name);
                                               arguments =
                                                 (interceptor_parameter_names
                                                 |> List.map (fun x ->
                                                        (Variable x
                                                          : Caml_light
                                                            .expression)))
                                                 @ [
                                                     Parenthesised
                                                       {
                                                         style = Parenthesis;
                                                         inner =
                                                           (match
                                                              initial_accumulator_constant
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

                                  [ new_definition; interceptor ])
                       |> List.concat;
                   })
         | _ -> phrase)
;;

print_endline (string_of_ast rectified)
