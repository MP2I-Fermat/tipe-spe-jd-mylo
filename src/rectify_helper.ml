open Caml_light
open Rectify

type rectify_result =
  | CouldNotComputeRectifyingSet
  | EmptyRectifyingSet
  | NewBindings of (binding list * bool) list * recursive_call_info option

let rectify_bindings (bindings : binding list) : rectify_result =
  let k = ref 0 in

  (* Step 1: Linearize *)
  let linearized_functions =
    bindings
    |> List.filter_map (fun (binding : binding) ->
           match binding with
           | Variable _ -> None
           | Function { name; parameters; body; return_type } ->
               let body_lin, k' = linearize body !k in
               k := k';
               Some
                 ( name,
                   FunctionLiteral
                     {
                       style = Fun;
                       cases = [ (parameters, body_lin) ];
                       return_type_for_delinearize = return_type;
                     } ))
  in

  (* Step 2: Calculate rectifying set *)
  match cloture_rectifiable linearized_functions with
  | None -> CouldNotComputeRectifyingSet
  | Some { rectifying_set = [] } -> EmptyRectifyingSet
  | Some { rectifying_set = cloture_rect } ->
      (* Step 3: Rectify *)
      let rectified_functions =
        rectify linearized_functions cloture_rect linearized_functions
      in

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
               | Variable _ -> (binding, None)
               | Function { name; parameters; body; return_type } ->
                   if not (List.mem name cloture_rect) then (binding, None)
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
                            return_type =
                              new_linearized_definition
                                .return_type_for_delinearize;
                          }
                         : Caml_light.binding)
                     in

                     let interceptor =
                       (Function
                          {
                            name;
                            parameters =
                              parameters
                              |> List.mapi (fun i parameter ->
                                     match get_name parameter with
                                     | Some _ -> parameter
                                     | None -> (
                                         match parameter with
                                         | Constant
                                             (Construction (Unit Parenthesis))
                                           ->
                                             parameter
                                         | _ -> Ident ("arg" ^ string_of_int i)));
                            body =
                              FunctionApplication
                                {
                                  receiver = Variable (new_name name);
                                  arguments =
                                    (parameters
                                    |> List.mapi (fun i parameter ->
                                           match get_name parameter with
                                           | Some name ->
                                               (Variable name : expression)
                                           | None -> (
                                               match parameter with
                                               | Constant
                                                   (Construction
                                                      (Unit Parenthesis)) ->
                                                   Constant
                                                     (Construction
                                                        (Unit Parenthesis))
                                               | _ ->
                                                   Variable
                                                     ("arg" ^ string_of_int i)))
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

                     (new_definition, Some interceptor))
        (* Rassemble tous les bindings de fonctions mutuellement récursives
         * puis ajoute les bindings d’intercepteurs juste après *)
        |> List.fold_left
             (fun l (new_def, interceptor) ->
               match (l, interceptor) with
               | [], Some i -> [ ([ new_def ], true); ([ i ], false) ]
               | [], None -> [ ([ new_def ], true) ]
               | (x, _) :: q, Some i ->
                   (new_def :: x, true) :: ([ i ], false) :: q
               | (x, _) :: q, None -> (new_def :: x, true) :: q)
             []
        |> fun l ->
        match l with
        | [] -> []
        | (x, x_is_rec) :: q -> (List.rev x, x_is_rec) :: q
      in
      NewBindings (rectified_bindings, cloture_rectifiable renamed_functions)

(* La fonction transform bindings prend le bindings et le is_rec et renvoie
 * les nouveaux bindings *)
let rec try_transform_bindings_deep (bindings : binding list) (is_rec : bool)
    (transform_bindings : binding list -> bool -> rectify_result) :
    (binding list * bool) list =
  match transform_bindings bindings is_rec with
  | NewBindings (b, _) -> b
  (* Only push deeper if we didn't fail to compute a rectifying set. If we did,
   * then we might be hiding recursive calls when we dig deeper (if a local
   * function calls a function defined in a higher scope). *)
  | CouldNotComputeRectifyingSet -> [ (bindings, is_rec) ]
  | EmptyRectifyingSet ->
      let transform_one_binding (binding : binding) =
        match binding with
        | Variable { lhs; value } ->
            ( [
                (Variable
                   {
                     lhs;
                     value = transform_bindings_in value transform_bindings;
                   }
                  : binding);
              ],
              false )
        | Function { name; parameters; body; return_type } ->
            ( [
                Function
                  {
                    name;
                    parameters;
                    body = transform_bindings_in body transform_bindings;
                    return_type;
                  };
              ],
              is_rec )
      in
      List.map transform_one_binding bindings

and transform_bindings_in (e : expression)
    (transform_bindings : binding list -> bool -> rectify_result) : expression =
  match e with
  | Variable _ -> e
  | Constant _ -> e
  | Parenthesised { inner; style } ->
      Parenthesised
        { style; inner = transform_bindings_in inner transform_bindings }
  | TypeCoercion { inner; typ } ->
      TypeCoercion
        { inner = transform_bindings_in inner transform_bindings; typ }
  | ListLiteral l ->
      ListLiteral
        (List.map (fun l -> transform_bindings_in l transform_bindings) l)
  | ArrayLiteral l ->
      ArrayLiteral
        (List.map (fun l -> transform_bindings_in l transform_bindings) l)
  | RecordLiteral r ->
      RecordLiteral
        (List.map
           (fun (n, e) -> (n, transform_bindings_in e transform_bindings))
           r)
  | WhileLoop { condition; body } ->
      WhileLoop
        {
          condition = transform_bindings_in condition transform_bindings;
          body = transform_bindings_in body transform_bindings;
        }
  | ForLoop { direction = direction'; variable; start; finish; body } ->
      ForLoop
        {
          direction = direction';
          variable;
          start = transform_bindings_in start transform_bindings;
          finish = transform_bindings_in finish transform_bindings;
          body = transform_bindings_in body transform_bindings;
        }
  | Dereference e -> Dereference (transform_bindings_in e transform_bindings)
  | FieldAccess { receiver; target } ->
      FieldAccess
        { receiver = transform_bindings_in receiver transform_bindings; target }
  | ArrayAccess { receiver; target } ->
      ArrayAccess
        {
          receiver = transform_bindings_in receiver transform_bindings;
          target = transform_bindings_in target transform_bindings;
        }
  | FunctionApplication { receiver; arguments } ->
      FunctionApplication
        {
          receiver = transform_bindings_in receiver transform_bindings;
          arguments =
            List.map
              (fun arg -> transform_bindings_in arg transform_bindings)
              arguments;
        }
  | PrefixOperation { receiver; operation } ->
      PrefixOperation
        {
          operation;
          receiver = transform_bindings_in receiver transform_bindings;
        }
  | InfixOperation { lhs; rhs; operation } ->
      InfixOperation
        {
          lhs = transform_bindings_in lhs transform_bindings;
          rhs = transform_bindings_in rhs transform_bindings;
          operation;
        }
  | Negation e -> Negation (transform_bindings_in e transform_bindings)
  | Tuple t ->
      Tuple (List.map (fun x -> transform_bindings_in x transform_bindings) t)
  | FieldAssignment { receiver; target; value } ->
      FieldAssignment
        {
          receiver = transform_bindings_in receiver transform_bindings;
          target;
          value = transform_bindings_in value transform_bindings;
        }
  | ArrayAssignment { receiver; target; value } ->
      ArrayAssignment
        {
          receiver = transform_bindings_in receiver transform_bindings;
          target = transform_bindings_in target transform_bindings;
          value = transform_bindings_in value transform_bindings;
        }
  | ReferenceAssignment { receiver; value } ->
      ReferenceAssignment
        {
          receiver = transform_bindings_in receiver transform_bindings;
          value = transform_bindings_in value transform_bindings;
        }
  | If { condition; body; else_body } ->
      If
        {
          condition = transform_bindings_in condition transform_bindings;
          body = transform_bindings_in body transform_bindings;
          else_body =
            Option.map
              (fun b -> transform_bindings_in b transform_bindings)
              else_body;
        }
  | Sequence s ->
      Sequence
        (List.map (fun e -> transform_bindings_in e transform_bindings) s)
  | Match { value; cases } ->
      Match
        {
          value = transform_bindings_in value transform_bindings;
          cases =
            List.map
              (fun (patterns, e) ->
                (patterns, transform_bindings_in e transform_bindings))
              cases;
        }
  | Try { value; cases } ->
      Try
        {
          value = transform_bindings_in value transform_bindings;
          cases =
            List.map
              (fun (patterns, e) ->
                (patterns, transform_bindings_in e transform_bindings))
              cases;
        }
  | FunctionLiteral { style; cases } ->
      FunctionLiteral
        {
          style;
          cases =
            List.map
              (fun (patterns, e) ->
                (patterns, transform_bindings_in e transform_bindings))
              cases;
        }
  | LetBinding { bindings; is_rec; inner } ->
      let new_bindings_list =
        try_transform_bindings_deep bindings is_rec transform_bindings
      in
      let rec flatten (inner_acc : expression)
          (bindings_list : (binding list * bool) list) =
        match bindings_list with
        | [] -> inner_acc
        | [ (new_bindings, new_is_rec) ] ->
            LetBinding
              {
                bindings = new_bindings;
                is_rec = new_is_rec;
                inner = inner_acc;
              }
        | (new_bindings, _) :: q ->
            flatten
              (LetBinding
                 { bindings = new_bindings; is_rec = false; inner = inner_acc })
              q
      in
      flatten
        (transform_bindings_in inner transform_bindings)
        (List.rev new_bindings_list)
  | StringAccess { receiver; target } ->
      StringAccess
        {
          receiver = transform_bindings_in receiver transform_bindings;
          target = transform_bindings_in target transform_bindings;
        }
  | StringAssignment { receiver; target; value } ->
      StringAssignment
        {
          receiver = transform_bindings_in receiver transform_bindings;
          target = transform_bindings_in target transform_bindings;
          value = transform_bindings_in value transform_bindings;
        }
