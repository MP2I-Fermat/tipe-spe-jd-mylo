open Caml_light
open Caml_light_utils

type value_declaration =
  | Variable of expression node
  | Function of {
      name : variable node;
      parameters : pattern node list;
      body : expression node;
    }

type scope = {
  parent_scope : scope option;
  value_declarations : (string, value_declaration) Hashtbl.t;
}

let rec scope_lookup (s : scope) (name : string) : value_declaration =
  match Hashtbl.find_opt s.value_declarations name with
  | Some d -> d
  | None -> (
      match s.parent_scope with
      | None -> failwith "Declaration not found in scope"
      | Some p -> scope_lookup p name)

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
  (* TODO: Check if any patterns shadow the function *)
  | Match { value; cases } ->
      contains_only_full_applications f value
      && List.for_all (fun (_, e) -> contains_only_full_applications f e) cases
  | Try { value; cases } ->
      contains_only_full_applications f value
      && List.for_all (fun (_, e) -> contains_only_full_applications f e) cases
  | FunctionLiteral { cases } ->
      List.for_all (fun (_, e) -> contains_only_full_applications f e) cases
  (* TODO: Check if any bindings shadow the function *)
  | LetBinding { bindings; inner } ->
      let check_binding (b : binding) : bool =
        match b with
        | Variable { value } -> contains_only_full_applications f value
        | Function f2 -> contains_only_full_applications f f2.body
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

let rec is_variable_pattern (p : pattern) : bool =
  match p with
  | Ident _ | As _ -> true
  | TypeCoercion { inner } | Parenthesised inner -> is_variable_pattern inner
  | _ -> false

let rec get_variable_pattern (p : pattern) : variable =
  match p with
  | Ident name | As { name } -> name
  | TypeCoercion { inner } | Parenthesised inner -> get_variable_pattern inner
  | _ -> failwith "Not a variable pattern"

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
  && List.for_all is_variable_pattern f.parameters

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
    | Match { value; cases } ->
        let count, value_items, value_name = linearize_items_from value count in
        let match_name = var_name count in
        ( count + 1,
          value_items
          @ [ (Ident match_name, Match { value = Variable value_name; cases }) ],
          match_name )
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
    | ListLiteral _ -> failwith "Unimplemented: linearize ListLiteral"
    | ArrayLiteral _ -> failwith "Unimplemented: linearize ArrayLiteral"
    | RecordLiteral _ -> failwith "Unimplemented: linearize RecordLiteral"
    | WhileLoop _ -> failwith "Unimplemented: linearize WhileLoop"
    | ForLoop _ -> failwith "Unimplemented: linearize ForLoop"
    | Dereference _ -> failwith "Unimplemented: linearize Dereference"
    | FieldAccess _ -> failwith "Unimplemented: linearize FieldAccess"
    | ArrayAccess _ -> failwith "Unimplemented: linearize ArrayAccess"
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
    | PrefixOperation _ -> failwith "Unimplemented: linearize PrefixOperation"
    | Negation _ -> failwith "Unimplemented: linearize Negation"
    | Tuple _ -> failwith "Unimplemented: linearize Tuple"
    | FieldAssignment _ -> failwith "Unimplemented: linearize FieldAssignment"
    | ArrayAssignment _ -> failwith "Unimplemented: linearize ArrayAssignment"
    | ReferenceAssignment _ ->
        failwith "Unimplemented: linearize ReferenceAssignment"
    | If _ -> failwith "Unimplemented: linearize If"
    | Sequence _ -> failwith "Unimplemented: linearize Sequence"
    | Try _ -> failwith "Unimplemented: linearize Try"
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
    | StringAccess _ -> failwith "Unimplemented: linearize StringAccess"
    | StringAssignment _ -> failwith "Unimplemented: linearize StringAssignment"
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
  and push_rectification_down (e : expression) : expression =
    match e with
    | Match { value; cases } ->
        Match
          {
            value;
            cases =
              List.map
                (fun (patterns, value) -> (patterns, rectify_expression value))
                cases;
          }
    | FunctionApplication
        { receiver = Caml_light.Variable receiver_name; arguments }
      when receiver_name = function_name ->
        FunctionApplication
          {
            receiver = Variable aux_name;
            arguments = arguments @ [ Variable "_aux_continue" ];
          }
    | _ -> e
  in

  {
    name = function_name;
    parameters;
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
                  (parameters
                  |> List.map get_variable_pattern
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
        let unable_to_check_for_rec (b : binding) : bool =
          match b with
          | Variable { lhs } -> not (is_variable_pattern lhs)
          | Function _ -> false
        in

        let binding_name (b : binding) : variable =
          match b with
          | Variable { lhs } -> get_variable_pattern lhs
          | Function { name } -> name
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
                     unable_to_check_for_rec binding
                     ||
                     let name = binding_name binding in
                     List.exists
                       (fun binding' ->
                         contains_reference name (binding_body binding'))
                       new_bindings)
                   new_bindings;
          }
    | _ -> p
  in

  List.map rectify_phrase p
