open Caml_light
open Caml_light_utils

type value_declaration =
  | Variable of expression node
  | Function of {
      name : variable node;
      parameters : pattern node list;
      body : expression node;
    }

let rec introduced_variables (p : pattern) =
  match p with
  | Ident i -> [ i ]
  | Underscore -> []
  | Parenthesised e -> introduced_variables e
  | TypeCoercion { inner } -> introduced_variables inner
  | Constant _ -> []
  | Record r -> List.concat_map (fun (_, p) -> introduced_variables p) r
  | List l -> List.concat_map introduced_variables l
  | Construction { argument } -> introduced_variables argument
  | Concatenation { head; tail } ->
      List.concat [ introduced_variables head; introduced_variables tail ]
  | Tuple t -> List.concat_map introduced_variables t
  | Or o -> List.concat_map introduced_variables o
  | As { inner } -> introduced_variables inner

let rec contains_only_full_applications (f : function_) (e : expression) : bool
    =
  match e with
  | Variable _ -> true
  | Constant _ -> true
  | Parenthesised { inner } -> contains_only_full_applications f inner
  | TypeCoercion { inner } -> contains_only_full_applications f inner
  | ListLiteral l -> List.for_all (contains_only_full_applications f) l
  | ArrayLiteral l -> List.for_all (contains_only_full_applications f) l
  | RecordLiteral l ->
      List.for_all (fun (_, e) -> contains_only_full_applications f e) l
  | WhileLoop { condition; body } ->
      contains_only_full_applications f condition
      && contains_only_full_applications f body
  | ForLoop { start; finish; body } ->
      contains_only_full_applications f start
      && contains_only_full_applications f finish
      && contains_only_full_applications f body
  | Dereference e -> contains_only_full_applications f e
  | FieldAccess { receiver } -> contains_only_full_applications f receiver
  | ArrayAccess { receiver; target } ->
      contains_only_full_applications f receiver
      && contains_only_full_applications f target
  | FunctionApplication { receiver; arguments } ->
      (match receiver with
      | Variable name when name = f.name ->
          List.length arguments = List.length f.parameters
      | _ -> true)
      && contains_only_full_applications f receiver
      && List.for_all (contains_only_full_applications f) arguments
  | PrefixOperation { receiver } -> contains_only_full_applications f receiver
  | InfixOperation { lhs; rhs } ->
      contains_only_full_applications f lhs
      && contains_only_full_applications f rhs
  | Negation e -> contains_only_full_applications f e
  | Tuple l -> List.for_all (contains_only_full_applications f) l
  | FieldAssignment { receiver; value } ->
      contains_only_full_applications f receiver
      && contains_only_full_applications f value
  | ArrayAssignment { receiver; target; value } ->
      contains_only_full_applications f receiver
      && contains_only_full_applications f target
      && contains_only_full_applications f value
  | ReferenceAssignment { receiver; value } ->
      contains_only_full_applications f receiver
      && contains_only_full_applications f value
  | If { condition; body; else_body } -> (
      contains_only_full_applications f condition
      && contains_only_full_applications f body
      &&
      match else_body with
      | None -> true
      | Some else_body -> contains_only_full_applications f else_body)
  | Sequence s -> List.for_all (contains_only_full_applications f) s
  | Match { value; cases } ->
      contains_only_full_applications f value
      && List.for_all
           (fun (p, e) ->
             p
             |> List.map introduced_variables
             |> List.flatten |> List.mem f.name
             || contains_only_full_applications f e)
           cases
  | Try { value; cases } ->
      contains_only_full_applications f value
      && List.for_all
           (fun (p, e) ->
             p
             |> List.map introduced_variables
             |> List.flatten |> List.mem f.name
             || contains_only_full_applications f e)
           cases
  | FunctionLiteral { cases } ->
      List.for_all
        (fun (p, e) ->
          p |> List.map introduced_variables |> List.flatten |> List.mem f.name
          || contains_only_full_applications f e)
        cases
  | LetBinding { bindings; inner } ->
      let check_binding (b : binding) : bool =
        match b with
        | Variable { lhs; value } ->
            List.mem f.name (introduced_variables lhs)
            || contains_only_full_applications f value
        | Function f2 ->
            f2.name = f.name
            || f2.parameters
               |> List.map introduced_variables
               |> List.flatten |> List.mem f.name
            || contains_only_full_applications f f2.body
      in
      contains_only_full_applications f inner
      && List.for_all check_binding bindings
  | StringAccess { receiver; target } ->
      contains_only_full_applications f receiver
      && contains_only_full_applications f target
  | StringAssignment { receiver; target; value } ->
      contains_only_full_applications f receiver
      && contains_only_full_applications f target
      && contains_only_full_applications f value

let contains_reference (v : variable) (e : expression) : bool =
  let contains = ref false in
  let _ =
    map_expression ~direction:Outwards
      (fun e ->
        (match e with Variable v' when v = v' -> contains := true | _ -> ());
        e)
      e
  in
  !contains

let is_rectify_candidate (f : function_) ~(binding_is_rec : bool) : bool =
  binding_is_rec
  && contains_reference f.name f.body
  && contains_only_full_applications f f.body

let is_simple_expression (e : expression) : bool =
  let res = ref true in
  let _ =
    map_expression
      (fun e' ->
        (res := e == e' || match e' with Variable _ -> true | _ -> false);
        e')
      e ~direction:Inwards
  in
  !res

let linearize (e : expression) : (pattern * expression) list * string =
  let var_name (count : int) : string = "_lin_" ^ string_of_int count in

  let rec linearize_items_from (e : expression) (count : int) :
      int * (pattern * expression) list * string =
    match e with
    | Variable v -> (count, [], v)
    | InfixOperation { lhs; operation; rhs } ->
        let count, lhs_items, lhs_name = linearize_items_from lhs count in
        let count, rhs_items, rhs_name = linearize_items_from rhs count in
        let op_name = var_name count in
        ( count + 1,
          lhs_items @ rhs_items
          @ [
              ( Ident op_name,
                InfixOperation
                  {
                    lhs = Variable lhs_name;
                    operation;
                    rhs = Variable rhs_name;
                  } );
            ],
          op_name )
    | Constant c ->
        let constant_name = var_name count in
        (count + 1, [ (Ident constant_name, Constant c) ], constant_name)
    | Parenthesised { inner } -> linearize_items_from inner count
    | TypeCoercion { inner; typ } ->
        let count, inner_items, inner_name = linearize_items_from inner count in
        let coercion_name = var_name count in
        ( count + 1,
          inner_items
          @ [
              ( Ident coercion_name,
                TypeCoercion { inner = Variable inner_name; typ } );
            ],
          coercion_name )
    | ListLiteral l ->
        let count, content_items, content_names =
          List.fold_left
            (fun (count, prev_literals, prev_names) element ->
              let count, element_literals, element_name =
                linearize_items_from element count
              in
              ( count,
                prev_literals @ element_literals,
                element_name :: prev_names ))
            (count, [], []) l
        in
        let list_name = var_name count in
        ( count + 1,
          content_items
          @ [
              ( Ident list_name,
                ListLiteral
                  (content_names
                  |> List.map (fun n -> (Variable n : expression))
                  |> List.rev) );
            ],
          list_name )
    | ArrayLiteral l ->
        let count, content_items, content_names =
          List.fold_left
            (fun (count, prev_literals, prev_names) element ->
              let count, element_literals, element_name =
                linearize_items_from element count
              in
              ( count,
                prev_literals @ element_literals,
                element_name :: prev_names ))
            (count, [], []) l
        in
        let array_name = var_name count in
        ( count + 1,
          content_items
          @ [
              ( Ident array_name,
                ArrayLiteral
                  (content_names
                  |> List.map (fun n -> (Variable n : expression))
                  |> List.rev) );
            ],
          array_name )
    | RecordLiteral r ->
        let count, content_items, contents =
          List.fold_left
            (fun (count, prev_literals, prev_names) (label, element) ->
              let count, element_literals, element_name =
                linearize_items_from element count
              in
              ( count,
                prev_literals @ element_literals,
                (label, (Variable element_name : expression)) :: prev_names ))
            (count, [], []) r
        in
        let record_name = var_name count in
        ( count + 1,
          content_items
          @ [ (Ident record_name, RecordLiteral (List.rev contents)) ],
          record_name )
    | WhileLoop _ -> failwith "Unimplemented: linearize WhileLoop"
    | ForLoop _ -> failwith "Unimplemented: linearize ForLoop"
    | Dereference e ->
        let count, e_items, e_name = linearize_items_from e count in
        let dereference_name = var_name count in
        ( count + 1,
          e_items @ [ (Ident dereference_name, Dereference (Variable e_name)) ],
          dereference_name )
    | FieldAccess { receiver; target } ->
        let count, receiver_items, receiver_name =
          linearize_items_from receiver count
        in
        let access_name = var_name count in
        ( count + 1,
          receiver_items
          @ [
              ( Ident access_name,
                FieldAccess { receiver = Variable receiver_name; target } );
            ],
          access_name )
    | ArrayAccess { receiver; target } ->
        let count, receiver_items, receiver_name =
          linearize_items_from receiver count
        in
        let target, target_items, target_name =
          linearize_items_from target count
        in
        let access_name = var_name count in
        ( count + 1,
          receiver_items @ target_items
          @ [
              ( Ident access_name,
                ArrayAccess
                  {
                    receiver = Variable receiver_name;
                    target = Variable target_name;
                  } );
            ],
          access_name )
    | FunctionApplication { receiver; arguments } ->
        let count, receiver_items, receiver_name =
          linearize_items_from receiver count
        in
        let count, arguments_items, arguments_name =
          List.fold_left
            (fun (count, arguments_items, arguments_names) argument ->
              let count, argument_items, argument_name =
                linearize_items_from argument count
              in
              ( count,
                arguments_items @ argument_items,
                arguments_names @ [ argument_name ] ))
            (count, [], []) arguments
        in
        let application_name = var_name count in
        ( count + 1,
          receiver_items @ arguments_items
          @ [
              ( Ident application_name,
                FunctionApplication
                  {
                    receiver = Variable receiver_name;
                    arguments =
                      List.map (fun v -> Caml_light.Variable v) arguments_name;
                  } );
            ],
          application_name )
    | PrefixOperation { receiver; operation } ->
        let count, receiver_items, receiver_name =
          linearize_items_from receiver count
        in
        let operation_name = var_name count in
        ( count + 1,
          receiver_items
          @ [
              ( Ident operation_name,
                PrefixOperation { operation; receiver = Variable receiver_name }
              );
            ],
          operation_name )
    | Negation receiver ->
        let count, receiver_items, receiver_name =
          linearize_items_from receiver count
        in
        let operation_name = var_name count in
        ( count + 1,
          receiver_items
          @ [ (Ident operation_name, Negation (Variable receiver_name)) ],
          operation_name )
    | Tuple t ->
        let count, content_literals, content_names =
          List.fold_left
            (fun (count, prev_literals, prev_names) element ->
              let count, element_literals, element_name =
                linearize_items_from element count
              in
              ( count,
                prev_literals @ element_literals,
                element_name :: prev_names ))
            (count, [], []) t
        in
        let list_name = var_name count in
        ( count + 1,
          content_literals
          @ [
              ( Ident list_name,
                Tuple
                  (content_names
                  |> List.map (fun n -> (Variable n : expression))
                  |> List.rev) );
            ],
          list_name )
    | FieldAssignment { receiver; target; value } ->
        let count, receiver_items, receiver_name =
          linearize_items_from receiver count
        in
        let count, value_items, value_name = linearize_items_from value count in
        let access_name = var_name count in
        ( count + 1,
          receiver_items @ value_items
          @ [
              ( Ident access_name,
                FieldAssignment
                  {
                    receiver = Variable receiver_name;
                    target;
                    value = Variable value_name;
                  } );
            ],
          access_name )
    | ArrayAssignment { receiver; target; value } ->
        let count, receiver_items, receiver_name =
          linearize_items_from receiver count
        in
        let target, target_items, target_name =
          linearize_items_from target count
        in
        let count, value_items, value_name = linearize_items_from value count in
        let access_name = var_name count in
        ( count + 1,
          receiver_items @ target_items
          @ [
              ( Ident access_name,
                ArrayAssignment
                  {
                    receiver = Variable receiver_name;
                    target = Variable target_name;
                    value = Variable value_name;
                  } );
            ],
          access_name )
    | ReferenceAssignment { receiver; value } ->
        let count, receiver_items, receiver_name =
          linearize_items_from receiver count
        in
        let count, value_items, value_name = linearize_items_from value count in
        let access_name = var_name count in
        ( count + 1,
          receiver_items @ value_items
          @ [
              ( Ident access_name,
                ReferenceAssignment
                  {
                    receiver = Variable receiver_name;
                    value = Variable value_name;
                  } );
            ],
          access_name )
    (* Branching expression *)
    | If { condition; body; else_body } ->
        let count, condition_items, condition_name =
          linearize_items_from condition count
        in
        let if_name = var_name count in
        ( count + 1,
          condition_items
          @ [
              ( Ident if_name,
                If { condition = Variable condition_name; body; else_body } );
            ],
          if_name )
    | Sequence l ->
        List.fold_left
          (fun (count, items, root) e ->
            let count, e_items, e_root = linearize_items_from e count in
            (count, items @ e_items, e_root))
          (count, [], "_") l
    (* Branching expression *)
    | Match { value; cases } ->
        let count, value_items, value_name = linearize_items_from value count in
        let match_name = var_name count in
        ( count + 1,
          value_items
          @ [ (Ident match_name, Match { value = Variable value_name; cases }) ],
          match_name )
    (* Branching expression *)
    | Try { value; cases } ->
        let count, value_items, value_name = linearize_items_from value count in
        let match_name = var_name count in
        ( count + 1,
          value_items
          @ [ (Ident match_name, Try { value = Variable value_name; cases }) ],
          match_name )
    | FunctionLiteral { style; cases } ->
        let function_name = var_name count in
        ( count + 1,
          [ (Ident function_name, FunctionLiteral { style; cases }) ],
          function_name )
    | LetBinding { bindings; is_rec; inner } ->
        let count, bindings_items =
          List.fold_left
            (fun (count, bindings_items) binding ->
              match binding with
              | (Caml_light.Variable { lhs; value } : binding) ->
                  if is_simple_expression value then
                    (count, bindings_items @ [ (lhs, value) ])
                  else
                    let count, value_items, value_name =
                      linearize_items_from value count
                    in
                    ( count,
                      bindings_items @ value_items
                      @ [ (lhs, Variable value_name) ] )
              | Function { name; parameters; body } ->
                  ( count,
                    [
                      ( Ident name,
                        FunctionLiteral
                          { style = Fun; cases = [ (parameters, body) ] } );
                    ] ))
            (count, []) bindings
        in
        let count, inner_items, inner_name = linearize_items_from inner count in
        (count, bindings_items @ inner_items, inner_name)
    | StringAccess { target; receiver } ->
        let count, receiver_items, receiver_name =
          linearize_items_from receiver count
        in
        let target, target_items, target_name =
          linearize_items_from target count
        in
        let access_name = var_name count in
        ( count + 1,
          receiver_items @ target_items
          @ [
              ( Ident access_name,
                StringAccess
                  {
                    receiver = Variable receiver_name;
                    target = Variable target_name;
                  } );
            ],
          access_name )
    | StringAssignment { receiver; target; value } ->
        let count, receiver_items, receiver_name =
          linearize_items_from receiver count
        in
        let target, target_items, target_name =
          linearize_items_from target count
        in
        let count, value_items, value_name = linearize_items_from value count in
        let access_name = var_name count in
        ( count + 1,
          receiver_items @ target_items
          @ [
              ( Ident access_name,
                StringAssignment
                  {
                    receiver = Variable receiver_name;
                    target = Variable target_name;
                    value = Variable value_name;
                  } );
            ],
          access_name )
  in
  let count, items, root = linearize_items_from e 0 in
  (items, root)

let rec delinearize ((items, root) : (pattern * expression) list * string) :
    expression =
  let collapsed_items =
    List.rev
      (List.fold_left
         (fun so_far (pattern, def) ->
           let substituted = ref [] in
           let linearized_def =
             map_expression ~direction:Outwards
               (fun e ->
                 match e with
                 | Variable v
                   when String.starts_with ~prefix:"_lin_" v
                        || v = "_aux_continue" || v = "_new_aux_continue" -> (
                     match List.assoc_opt (Ident v) so_far with
                     | Some def ->
                         substituted := v :: !substituted;
                         Parenthesised { inner = def; style = Parenthesis }
                     | None -> Variable v)
                 | _ -> e)
               def
           in
           let filtered_decls =
             List.filter
               (fun (pattern, _) ->
                 match pattern with
                 | Ident v -> not (List.mem v !substituted)
                 | _ -> true)
               so_far
           in
           (pattern, linearized_def) :: filtered_decls)
         [] items)
  in

  let rec delinearize_items (items : (pattern * expression) list)
      (root : expression) : expression =
    match items with
    | (pattern, def) :: q -> (
        let q_expression = delinearize_items q root in
        match q_expression with
        | Variable v when Ident v = pattern -> def
        | _ ->
            let is_rec =
              match pattern with
              | Ident v -> (
                  match def with
                  | FunctionLiteral _ -> contains_reference v def
                  | _ -> false)
              | _ -> false
            in
            LetBinding
              {
                is_rec;
                bindings = [ Variable { lhs = pattern; value = def } ];
                inner = q_expression;
              })
    | [] -> root
  in

  delinearize_items collapsed_items (Variable root)

let rectify ({ name = function_name; parameters; body } : function_) : function_
    =
  let aux_name = function_name ^ "_aux" in

  let id_function : expression =
    Parenthesised
      {
        style = Parenthesis;
        inner =
          FunctionLiteral
            {
              style = Fun;
              cases = [ ([ Ident "_aux_ret" ], Variable "_aux_ret") ];
            };
      }
  in

  let rec rectify_linear
      ((items, root) : (pattern * expression) list * variable) :
      (pattern * expression) list * variable =
    match items with
    | [] ->
        ( [
            ( Ident "_lin_ret",
              FunctionApplication
                {
                  receiver = Variable "_aux_continue";
                  arguments = [ Variable root ];
                } );
          ],
          "_lin_ret" )
    | (name, value) :: q ->
        if contains_reference function_name value then
          if q <> [] || Ident root <> name then
            let new_continuation_body =
              rectify_expression (delinearize (q, root))
            in
            ( [
                ( Ident "_new_aux_continue",
                  FunctionLiteral
                    {
                      style = Fun;
                      cases = [ ([ name ], new_continuation_body) ];
                    } );
                (Ident "_aux_continue", Variable "_new_aux_continue");
                (Ident "_lin_ret", push_rectification_down value);
              ],
              "_lin_ret" )
          else
            ([ (Ident "_lin_ret", push_rectification_down value) ], "_lin_ret")
        else
          let inner_items, inner_root = rectify_linear (q, root) in
          ((name, value) :: inner_items, inner_root)
  and rectify_expression (e : expression) : expression =
    delinearize (rectify_linear (linearize e))
  (* Pushes rectification down into branching expressions that cannot be linearized. *)
  and push_rectification_down (e : expression) : expression =
    match e with
    (* Substitute calls to original function with calls to auxiliary function here. *)
    | FunctionApplication
        { receiver = Caml_light.Variable receiver_name; arguments }
      when receiver_name = function_name ->
        FunctionApplication
          {
            receiver = Variable aux_name;
            arguments = arguments @ [ Variable "_aux_continue" ];
          }
    | Match { value; cases } ->
        Match
          {
            value;
            cases =
              List.map
                (fun (patterns, value) -> (patterns, rectify_expression value))
                cases;
          }
    | If { condition; body; else_body } ->
        If
          {
            condition;
            body = rectify_expression body;
            else_body =
              (match else_body with
              | None -> None
              | Some e -> Some (rectify_expression e));
          }
    | Try { value; cases } ->
        Try
          {
            value;
            cases =
              List.map
                (fun (patterns, value) -> (patterns, rectify_expression value))
                cases;
          }
    | _ -> e
  in

  let new_parameters =
    List.mapi
      (fun i pattern ->
        match pattern with Ident v -> v | _ -> "_arg_" ^ string_of_int i)
      parameters
  in

  {
    name = function_name;
    parameters = List.map (fun name -> Ident name) new_parameters;
    body =
      LetBinding
        {
          bindings =
            [
              Function
                {
                  name = aux_name;
                  parameters =
                    parameters
                    @ [
                        Parenthesised
                          (TypeCoercion
                             {
                               inner = Ident "_aux_continue";
                               typ =
                                 Function
                                   {
                                     argument = Argument "aux_continue_type";
                                     result = Argument "aux_continue_type";
                                   };
                             });
                      ];
                  body = rectify_expression body;
                };
            ];
          is_rec = true;
          inner =
            FunctionApplication
              {
                receiver = Variable aux_name;
                arguments =
                  (new_parameters
                  |> List.map (fun v -> (Variable v : expression)))
                  @ [ id_function ];
              };
        };
  }

let rectify_program (p : program) : program =
  let rec rectify_expression (e : expression) : expression =
    map_expression
      (fun e ->
        match e with
        | LetBinding { bindings; is_rec; inner } ->
            LetBinding
              {
                bindings =
                  List.map (rectify_binding ~binding_is_rec:is_rec) bindings;
                is_rec;
                inner;
              }
        | _ -> e)
      e ~direction:Outwards
  and rectify_binding (b : binding) ~(binding_is_rec : bool) : binding =
    match b with
    | Variable { lhs; value } ->
        Variable { lhs; value = rectify_expression value }
    | Function { name; parameters; body } ->
        let f' = { name; parameters; body = rectify_expression body } in
        if is_rectify_candidate f' ~binding_is_rec then Function (rectify f')
        else Function f'
  in

  let rectify_phrase (p : phrase) : phrase =
    match p with
    | Expression e -> Expression (rectify_expression e)
    | ValueDefinition { bindings; is_rec } ->
        let binding_names (b : binding) : variable list =
          match b with
          | Variable { lhs } -> introduced_variables lhs
          | Function { name } -> [ name ]
        in

        let binding_body (b : binding) : expression =
          match b with Variable { value } -> value | Function { body } -> body
        in

        let new_bindings =
          List.map (rectify_binding ~binding_is_rec:is_rec) bindings
        in
        ValueDefinition
          {
            bindings = new_bindings;
            is_rec =
              is_rec
              && List.exists
                   (fun binding ->
                     let names = binding_names binding in
                     List.exists
                       (fun binding' ->
                         List.exists
                           (fun name ->
                             contains_reference name (binding_body binding'))
                           names)
                       new_bindings)
                   new_bindings;
          }
    | _ -> p
  in

  List.map rectify_phrase p
