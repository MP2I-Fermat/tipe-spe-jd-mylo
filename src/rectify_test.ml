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

type rectify_result =
  | CouldNotComputeRectifyingSet
  | EmptyRectifyingSet
  | NewBindings of binding list

let rectify_bindings (bindings : binding list) : rectify_result =
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
                     { style = Fun; cases = [ (parameters, body_lin) ] } ))
  in

  (* Step 2: Calculate rectifying set *)
  match cloture_rectifiable linearized_functions with
  | None -> CouldNotComputeRectifyingSet
  | Some [] -> EmptyRectifyingSet
  | Some cloture_rect ->
      (* Step 3: Rectify *)
      let rectified_functions = rectify linearized_functions cloture_rect in

      (* Step 4: Replace continuations with accumulators (if possible) *)
      let accumulator_functions, initial_accumulator_constant =
        (* Step 4a: Extract all continuations *)
        match find_continuations rectified_functions cloture_rect with
        | None -> (rectified_functions, None)
        | Some continuations -> (
            (* Step 4b: Extract composition with previous continuation form each continuation *)
            let extracted_continuations =
              continuations |> List.filter_map extract_continuation_composition
            in

            if List.length extracted_continuations <> List.length continuations
            then (rectified_functions, None)
            else
              (* Step 4c: Find the initial constant to use *)
              let initial_constant = find_initials rectified_functions in
              match initial_constant with
              | None -> (rectified_functions, None)
              | Some (variables, initial) ->
                  (* Step 4d: Check continuations can commute *)
                  if commutes extracted_continuations && List.length initial = 1
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

      let rectified_bindings =
        bindings
        |> List.map (fun (binding : binding) ->
               match binding with
               | Variable _ -> [ binding ]
               | Function { name; parameters; body; return_type } ->
                   if not (List.mem name cloture_rect) then [ binding ]
                   else
                     let new_linearized_definition =
                       match List.assoc (new_name name) renamed_functions with
                       | FunctionLiteral f -> f
                       | _ -> failwith "Unable to find redefined definition"
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
                            body = fst (delinearize new_linearized_body []);
                            (* The return type depends on the return type of the continuation *)
                            return_type = None;
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
                                  receiver = Variable (new_name name);
                                  arguments =
                                    (interceptor_parameter_names
                                    |> List.map (fun x ->
                                           (Variable x : Caml_light.expression))
                                    )
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
                                                          ( [ Ident "res" ],
                                                            Variable "res" );
                                                        ];
                                                    }
                                              | Some cst -> Constant cst);
                                          };
                                      ];
                                };
                            return_type;
                          }
                         : Caml_light.binding)
                     in

                     [ new_definition; interceptor ])
        |> List.concat
      in
      NewBindings rectified_bindings

let rec try_rectify_bindings_deep (bindings : binding list) : binding list =
  match rectify_bindings bindings with
  | NewBindings b -> b
  (* Only push deeper if we didn't fail to compute a rectifying set. If we did,
    then we might be hiding recursive calls when we dig deeper (if a local
      function calls a function defined in a higher scope). *)
  | CouldNotComputeRectifyingSet -> bindings
  | EmptyRectifyingSet ->
      bindings
      |> List.map (fun (binding : binding) ->
             match binding with
             | Variable { lhs; value } ->
                 (Variable { lhs; value = rectify_bindings_in value } : binding)
             | Function { name; parameters; body; return_type } ->
                 Function
                   {
                     name;
                     parameters;
                     body = rectify_bindings_in body;
                     return_type;
                   })

and rectify_bindings_in (e : expression) : expression =
  match e with
  | Variable _ -> e
  | Constant _ -> e
  | Parenthesised { inner; style } ->
      Parenthesised { style; inner = rectify_bindings_in inner }
  | TypeCoercion { inner; typ } ->
      TypeCoercion { inner = rectify_bindings_in inner; typ }
  | ListLiteral l -> ListLiteral (List.map (fun l -> rectify_bindings_in l) l)
  | ArrayLiteral l -> ArrayLiteral (List.map (fun l -> rectify_bindings_in l) l)
  | RecordLiteral r ->
      RecordLiteral (List.map (fun (n, e) -> (n, rectify_bindings_in e)) r)
  | WhileLoop { condition; body } ->
      WhileLoop
        {
          condition = rectify_bindings_in condition;
          body = rectify_bindings_in body;
        }
  | ForLoop { direction = direction'; variable; start; finish; body } ->
      ForLoop
        {
          direction = direction';
          variable;
          start = rectify_bindings_in start;
          finish = rectify_bindings_in finish;
          body = rectify_bindings_in body;
        }
  | Dereference e -> Dereference (rectify_bindings_in e)
  | FieldAccess { receiver; target } ->
      FieldAccess { receiver = rectify_bindings_in receiver; target }
  | ArrayAccess { receiver; target } ->
      ArrayAccess
        {
          receiver = rectify_bindings_in receiver;
          target = rectify_bindings_in target;
        }
  | FunctionApplication { receiver; arguments } ->
      FunctionApplication
        {
          receiver = rectify_bindings_in receiver;
          arguments = List.map (fun arg -> rectify_bindings_in arg) arguments;
        }
  | PrefixOperation { receiver; operation } ->
      PrefixOperation { operation; receiver = rectify_bindings_in receiver }
  | InfixOperation { lhs; rhs; operation } ->
      InfixOperation
        {
          lhs = rectify_bindings_in lhs;
          rhs = rectify_bindings_in rhs;
          operation;
        }
  | Negation e -> Negation (rectify_bindings_in e)
  | Tuple t -> Tuple (List.map (fun l -> rectify_bindings_in l) t)
  | FieldAssignment { receiver; target; value } ->
      FieldAssignment
        {
          receiver = rectify_bindings_in receiver;
          target;
          value = rectify_bindings_in value;
        }
  | ArrayAssignment { receiver; target; value } ->
      ArrayAssignment
        {
          receiver = rectify_bindings_in receiver;
          target = rectify_bindings_in target;
          value = rectify_bindings_in value;
        }
  | ReferenceAssignment { receiver; value } ->
      ReferenceAssignment
        {
          receiver = rectify_bindings_in receiver;
          value = rectify_bindings_in value;
        }
  | If { condition; body; else_body } ->
      If
        {
          condition = rectify_bindings_in condition;
          body = rectify_bindings_in body;
          else_body = Option.map (fun b -> rectify_bindings_in b) else_body;
        }
  | Sequence s -> Sequence (List.map (fun e -> rectify_bindings_in e) s)
  | Match { value; cases } ->
      Match
        {
          value = rectify_bindings_in value;
          cases =
            List.map
              (fun (patterns, e) -> (patterns, rectify_bindings_in e))
              cases;
        }
  | Try { value; cases } ->
      Try
        {
          value = rectify_bindings_in value;
          cases =
            List.map
              (fun (patterns, e) -> (patterns, rectify_bindings_in e))
              cases;
        }
  | FunctionLiteral { style; cases } ->
      FunctionLiteral
        {
          style;
          cases =
            List.map
              (fun (patterns, e) -> (patterns, rectify_bindings_in e))
              cases;
        }
  | LetBinding { bindings; is_rec; inner } ->
      LetBinding
        {
          bindings = try_rectify_bindings_deep bindings;
          is_rec;
          inner = rectify_bindings_in inner;
        }
  | StringAccess { receiver; target } ->
      StringAccess
        {
          receiver = rectify_bindings_in receiver;
          target = rectify_bindings_in target;
        }
  | StringAssignment { receiver; target; value } ->
      StringAssignment
        {
          receiver = rectify_bindings_in receiver;
          target = rectify_bindings_in target;
          value = rectify_bindings_in value;
        }

let rectified =
  program
  |> List.map (fun phrase ->
         match phrase with
         | ValueDefinition { bindings; is_rec } ->
             ValueDefinition
               { is_rec; bindings = try_rectify_bindings_deep bindings }
         | _ -> phrase)
;;

print_endline (string_of_ast rectified)
