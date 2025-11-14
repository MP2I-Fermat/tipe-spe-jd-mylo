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
    map_expression
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

let rectify ({ name; parameters; body } as f : function_) : function_ =
  let aux_name = name ^ "_aux" in

  let rec replace_invocations (f : function_) (e : expression) : expression =
    map_expression
      (fun e ->
        match e with
        | FunctionApplication { receiver = Variable v; arguments }
          when v = f.name ->
            FunctionApplication
              {
                receiver = Variable aux_name;
                arguments =
                  arguments
                  @ [
                      Parenthesised
                        {
                          style = Parenthesis;
                          inner =
                            FunctionLiteral
                              {
                                style = Fun;
                                cases = [ ([ Ident "x" ], Variable "x") ];
                              };
                        };
                    ];
              }
        | _ -> e)
      e
  in

  {
    name;
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
                               inner = Ident "aux_continue";
                               typ =
                                 Function
                                   {
                                     argument = Argument "aux_continue_type";
                                     result = Argument "aux_continue_type";
                                   };
                             });
                      ];
                  body =
                    FunctionApplication
                      {
                        receiver = Variable "aux_continue";
                        arguments =
                          [
                            Parenthesised
                              {
                                style = Parenthesis;
                                inner = replace_invocations f body;
                              };
                          ];
                      };
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
                  @ [
                      Parenthesised
                        {
                          style = Parenthesis;
                          inner =
                            FunctionLiteral
                              {
                                style = Fun;
                                cases = [ ([ Ident "x" ], Variable "x") ];
                              };
                        };
                    ];
              };
        };
  }

let rectify_program (p : program) : program =
  let rec rectify_expression (e : expression) : expression = e
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
