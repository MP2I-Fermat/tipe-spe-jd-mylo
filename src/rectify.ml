open Caml_light
open Caml_light_utils

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

let binding_names (b : binding) : variable list =
  match b with
  | Variable { lhs } -> introduced_variables lhs
  | Function { name } -> [ name ]

let binding_body (b : binding) : expression =
  match b with Variable { value } -> value | Function { body } -> body

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

let rec contains_direct_access (f : string) (e : expression) : bool =
  match e with
  | Variable v -> v = f
  | Constant _ -> false
  | Parenthesised { inner } -> contains_direct_access f inner
  | TypeCoercion { inner } -> contains_direct_access f inner
  | ListLiteral l -> List.exists (contains_direct_access f) l
  | ArrayLiteral l -> List.exists (contains_direct_access f) l
  | RecordLiteral l -> List.exists (fun (_, e) -> contains_direct_access f e) l
  | WhileLoop { condition; body } ->
      contains_direct_access f condition || contains_direct_access f body
  | ForLoop { start; finish; body } ->
      contains_direct_access f start
      || contains_direct_access f finish
      || contains_direct_access f body
  | Dereference e -> contains_direct_access f e
  | FieldAccess { receiver } -> contains_direct_access f receiver
  | ArrayAccess { receiver; target } ->
      contains_direct_access f receiver || contains_direct_access f target
  | FunctionApplication { receiver; arguments } ->
      contains_direct_access f receiver
      || List.exists (contains_direct_access f) arguments
  | PrefixOperation { receiver } -> contains_direct_access f receiver
  | InfixOperation { lhs; rhs } ->
      contains_direct_access f lhs || contains_direct_access f rhs
  | Negation e -> contains_direct_access f e
  | Tuple l -> List.exists (contains_direct_access f) l
  | FieldAssignment { receiver; value } ->
      contains_direct_access f receiver || contains_direct_access f value
  | ArrayAssignment { receiver; target; value } ->
      contains_direct_access f receiver
      || contains_direct_access f target
      || contains_direct_access f value
  | ReferenceAssignment { receiver; value } ->
      contains_direct_access f receiver || contains_direct_access f value
  | If { condition; body; else_body } -> (
      contains_direct_access f condition
      || contains_direct_access f body
      ||
      match else_body with
      | None -> true
      | Some else_body -> contains_direct_access f else_body)
  | Sequence s -> List.exists (contains_direct_access f) s
  | Match { value; cases } ->
      contains_direct_access f value
      || List.exists
           (fun (p, e) ->
             p |> List.map introduced_variables |> List.flatten |> List.mem f
             || contains_direct_access f e)
           cases
  | Try { value; cases } ->
      contains_direct_access f value
      || List.exists
           (fun (p, e) ->
             p |> List.map introduced_variables |> List.flatten |> List.mem f
             || contains_direct_access f e)
           cases
  | FunctionLiteral _ -> false
  | LetBinding { bindings; inner } ->
      let check_binding (b : binding) : bool =
        match b with
        | Variable { lhs; value } ->
            List.mem f (introduced_variables lhs)
            || contains_direct_access f value
        | Function _ -> false
      in
      contains_direct_access f inner || List.exists check_binding bindings
  | StringAccess { receiver; target } ->
      contains_direct_access f receiver || contains_direct_access f target
  | StringAssignment { receiver; target; value } ->
      contains_direct_access f receiver
      || contains_direct_access f target
      || contains_direct_access f value

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

let linearize (e : expression) : binding list list * variable =
  let var_name (count : int) : variable = "_lin_" ^ string_of_int count in

  let rec linearize_items_from (e : expression) (count : int) :
      int * binding list list * variable =
    match e with
    | Variable v -> (count, [], v)
    | InfixOperation { lhs; operation; rhs } ->
        let count, lhs_items, lhs_name = linearize_items_from lhs count in
        let count, rhs_items, rhs_name = linearize_items_from rhs count in
        let op_name = var_name count in
        ( count + 1,
          lhs_items @ rhs_items
          @ [
              [
                Variable
                  {
                    lhs = Ident op_name;
                    value =
                      InfixOperation
                        {
                          lhs = Variable lhs_name;
                          operation;
                          rhs = Variable rhs_name;
                        };
                  };
              ];
            ],
          op_name )
    | Constant c ->
        let constant_name = var_name count in
        ( count + 1,
          [ [ Variable { lhs = Ident constant_name; value = Constant c } ] ],
          constant_name )
    | Parenthesised { inner } -> linearize_items_from inner count
    | TypeCoercion { inner; typ } ->
        let count, inner_items, inner_name = linearize_items_from inner count in
        let coercion_name = var_name count in
        ( count + 1,
          inner_items
          @ [
              [
                Variable
                  {
                    lhs = Ident coercion_name;
                    value = TypeCoercion { inner = Variable inner_name; typ };
                  };
              ];
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
              [
                Variable
                  {
                    lhs = Ident list_name;
                    value =
                      ListLiteral
                        (content_names
                        |> List.map (fun n -> (Variable n : expression))
                        |> List.rev);
                  };
              ];
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
              [
                Variable
                  {
                    lhs = Ident array_name;
                    value =
                      ArrayLiteral
                        (content_names
                        |> List.map (fun n -> (Variable n : expression))
                        |> List.rev);
                  };
              ];
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
          @ [
              [
                Variable
                  {
                    lhs = Ident record_name;
                    value = RecordLiteral (List.rev contents);
                  };
              ];
            ],
          record_name )
    | WhileLoop _ -> failwith "Unimplemented: linearize WhileLoop"
    | ForLoop _ -> failwith "Unimplemented: linearize ForLoop"
    | Dereference e ->
        let count, e_items, e_name = linearize_items_from e count in
        let dereference_name = var_name count in
        ( count + 1,
          e_items
          @ [
              [
                Variable
                  {
                    lhs = Ident dereference_name;
                    value = Dereference (Variable e_name);
                  };
              ];
            ],
          dereference_name )
    | FieldAccess { receiver; target } ->
        let count, receiver_items, receiver_name =
          linearize_items_from receiver count
        in
        let access_name = var_name count in
        ( count + 1,
          receiver_items
          @ [
              [
                Variable
                  {
                    lhs = Ident access_name;
                    value =
                      FieldAccess { receiver = Variable receiver_name; target };
                  };
              ];
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
              [
                Variable
                  {
                    lhs = Ident access_name;
                    value =
                      ArrayAccess
                        {
                          receiver = Variable receiver_name;
                          target = Variable target_name;
                        };
                  };
              ];
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
              [
                Variable
                  {
                    lhs = Ident application_name;
                    value =
                      FunctionApplication
                        {
                          receiver = Variable receiver_name;
                          arguments =
                            List.map
                              (fun v -> Caml_light.Variable v)
                              arguments_name;
                        };
                  };
              ];
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
              [
                Variable
                  {
                    lhs = Ident operation_name;
                    value =
                      PrefixOperation
                        { operation; receiver = Variable receiver_name };
                  };
              ];
            ],
          operation_name )
    | Negation receiver ->
        let count, receiver_items, receiver_name =
          linearize_items_from receiver count
        in
        let operation_name = var_name count in
        ( count + 1,
          receiver_items
          @ [
              [
                Variable
                  {
                    lhs = Ident operation_name;
                    value = Negation (Variable receiver_name);
                  };
              ];
            ],
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
              [
                Variable
                  {
                    lhs = Ident list_name;
                    value =
                      Tuple
                        (content_names
                        |> List.map (fun n -> (Variable n : expression))
                        |> List.rev);
                  };
              ];
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
              [
                Variable
                  {
                    lhs = Ident access_name;
                    value =
                      FieldAssignment
                        {
                          receiver = Variable receiver_name;
                          target;
                          value = Variable value_name;
                        };
                  };
              ];
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
              [
                Variable
                  {
                    lhs = Ident access_name;
                    value =
                      ArrayAssignment
                        {
                          receiver = Variable receiver_name;
                          target = Variable target_name;
                          value = Variable value_name;
                        };
                  };
              ];
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
              [
                Variable
                  {
                    lhs = Ident access_name;
                    value =
                      ReferenceAssignment
                        {
                          receiver = Variable receiver_name;
                          value = Variable value_name;
                        };
                  };
              ];
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
              [
                Variable
                  {
                    lhs = Ident if_name;
                    value =
                      If
                        { condition = Variable condition_name; body; else_body };
                  };
              ];
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
          @ [
              [
                Variable
                  {
                    lhs = Ident match_name;
                    value = Match { value = Variable value_name; cases };
                  };
              ];
            ],
          match_name )
    (* Branching expression *)
    | Try { value; cases } ->
        let count, value_items, value_name = linearize_items_from value count in
        let match_name = var_name count in
        ( count + 1,
          value_items
          @ [
              [
                Variable
                  {
                    lhs = Ident match_name;
                    value = Try { value = Variable value_name; cases };
                  };
              ];
            ],
          match_name )
    (* Branching expression *)
    | FunctionLiteral { style; cases } ->
        let function_name = var_name count in
        ( count + 1,
          [
            [
              Variable
                {
                  lhs = Ident function_name;
                  value = FunctionLiteral { style; cases };
                };
            ];
          ],
          function_name )
    | LetBinding { bindings; is_rec; inner } ->
        let count, bindings_items, bindings =
          List.fold_left
            (fun (count, bindings_items, bindings) binding ->
              match binding with
              | (Variable { lhs; value } : binding) ->
                  if is_simple_expression value then
                    (count, bindings_items, bindings @ [ binding ])
                  else
                    let count, items, value_name =
                      linearize_items_from value count
                    in
                    ( count,
                      bindings_items @ items,
                      bindings
                      @ [ Variable { lhs; value = Variable value_name } ] )
              (* Branching expression *)
              | Function _ -> (count, bindings_items, bindings @ [ binding ]))
            (count, [], []) bindings
        in
        let count, inner_items, inner_name = linearize_items_from inner count in
        (count, bindings_items @ [ bindings ] @ inner_items, inner_name)
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
              [
                Variable
                  {
                    lhs = Ident access_name;
                    value =
                      StringAccess
                        {
                          receiver = Variable receiver_name;
                          target = Variable target_name;
                        };
                  };
              ];
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
              [
                Variable
                  {
                    lhs = Ident access_name;
                    value =
                      StringAssignment
                        {
                          receiver = Variable receiver_name;
                          target = Variable target_name;
                          value = Variable value_name;
                        };
                  };
              ];
            ],
          access_name )
  in
  let count, items, root = linearize_items_from e 0 in
  (items, root)

let rec delinearize ((items, root) : binding list list * string) : expression =
  let find_binding_definition (l : binding list list) (v : variable) :
      expression option =
    let flat = List.flatten l in
    let rec find_definition (l : binding list) : expression option =
      match l with
      | [] -> None
      | Variable { lhs; value } :: q when lhs = Ident v -> Some value
      | _ :: q -> find_definition q
    in
    find_definition flat
  in

  let collapsed_items =
    items
    |> List.fold_left
         (fun so_far bindings ->
           let substituted = ref [] in

           let substitute_linear_variables (e : expression) : expression =
             map_expression ~direction:Outwards
               (fun e ->
                 match e with
                 | Variable v
                   when String.starts_with ~prefix:"_lin_" v
                        || String.starts_with ~prefix:"_aux_continue" v
                        || String.starts_with ~prefix:"_new_aux_continue" v -> (
                     match find_binding_definition so_far v with
                     | Some def ->
                         substituted := v :: !substituted;
                         Parenthesised { inner = def; style = Parenthesis }
                     | None -> Variable v)
                 | _ -> e)
               e
           in

           let linearized_bindings =
             bindings
             |> List.map (fun binding ->
                    match binding with
                    | (Variable { lhs; value } : binding) ->
                        (Variable
                           { lhs; value = substitute_linear_variables value }
                          : binding)
                    | Function { name; parameters; body } ->
                        Function
                          {
                            name;
                            parameters;
                            body = substitute_linear_variables body;
                          })
           in

           let filtered_decls =
             so_far
             |> List.map (fun bindings ->
                    bindings
                    |> List.filter (fun binding ->
                           match binding with
                           | (Variable { lhs = Ident v } : binding) ->
                               not (List.mem v !substituted)
                           | _ -> true))
             |> List.filter (fun bindings -> bindings <> [])
           in
           linearized_bindings :: filtered_decls)
         []
    |> List.rev
  in

  let rec delinearize_items (items : binding list list) (root : expression) :
      expression =
    match items with
    | bindings :: q -> (
        let q_expression = delinearize_items q root in

        match (bindings, q_expression) with
        | [ Variable { lhs = Ident v1; value } ], Variable v2 when v1 = v2 ->
            value
        | _ ->
            let is_rec =
              List.exists
                (fun binding ->
                  let names = binding_names binding in
                  List.exists
                    (fun binding' ->
                      List.exists
                        (fun name ->
                          contains_reference name (binding_body binding'))
                        names)
                    bindings)
                bindings
            in

            LetBinding { is_rec; bindings; inner = q_expression })
    | [] -> root
  in

  delinearize_items collapsed_items (Variable root)

let rectify ({ name = function_name; parameters; body } : function_) : function_
    =
  let aux_name = function_name ^ "_aux" in
  let aux_continue_name =
    "_aux_continue" ^ string_of_int (List.length parameters)
  in

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

  let rec rectify_linear ((items, root) : binding list list * variable) :
      binding list list * variable =
    match items with
    | [] ->
        ( [
            [
              Variable
                {
                  lhs = Ident "_lin_ret";
                  value =
                    FunctionApplication
                      {
                        receiver = Variable aux_continue_name;
                        arguments = [ Variable root ];
                      };
                };
            ];
          ],
          "_lin_ret" )
    | bindings :: q -> (
        (* Bindings is either:
           - A single binding containing a recursive call either directly or indirectly (i.e a function application or a match statement).
           - A set of indirectly self-referential bindings that can only contain recursive calls in their lazily evaluated code (i.e function bodies).
        *)
        match bindings with
        | [ (Variable { lhs; value } as binding) ]
          when contains_direct_access function_name value ->
            if introduced_variables lhs = [ root ] then
              ([ [ push_rectification_down binding ] ], root)
            else
              let new_continuation_body =
                rectify_expression (delinearize (q, root))
              in

              ( [
                  [
                    Variable
                      {
                        lhs = Ident ("_new" ^ aux_continue_name);
                        value =
                          FunctionLiteral
                            {
                              style = Fun;
                              cases = [ ([ lhs ], new_continuation_body) ];
                            };
                      };
                  ];
                  [
                    Variable
                      {
                        lhs = Ident aux_continue_name;
                        value = Variable ("_new" ^ aux_continue_name);
                      };
                  ];
                  [
                    push_rectification_down
                      (Variable { lhs = Ident "_lin_ret"; value });
                  ];
                ],
                "_lin_ret" )
        | _ ->
            let inner_items, inner_root = rectify_linear (q, root) in
            ( List.map push_rectification_down bindings :: inner_items,
              inner_root ))
  and rectify_expression (e : expression) : expression =
    delinearize (rectify_linear (linearize e))
  (* Pushes rectification down into branching expressions that cannot be linearized. *)
  and push_rectification_down (b : binding) : binding =
    match b with
    | Variable { lhs; value } ->
        let new_value =
          match value with
          (* Substitute calls to original function with calls to auxiliary function here. *)
          | FunctionApplication
              { receiver = Caml_light.Variable receiver_name; arguments }
            when receiver_name = function_name ->
              FunctionApplication
                {
                  receiver = Variable aux_name;
                  arguments = arguments @ [ Variable aux_continue_name ];
                }
          | Match { value; cases } ->
              Match
                {
                  value;
                  cases =
                    List.map
                      (fun (patterns, value) ->
                        (patterns, rectify_expression value))
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
                      (fun (patterns, value) ->
                        (patterns, rectify_expression value))
                      cases;
                }
          | FunctionLiteral { style; cases } ->
              failwith
                "Cannot push rectification into a function (mutually recursive \
                 functions are not implemented yet)"
          | _ -> value
        in
        Variable { lhs; value = new_value }
    | Function _ ->
        failwith
          "Cannot push rectification into a function (mutually recursive \
           functions are not implemented yet)"
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
                               inner = Ident aux_continue_name;
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
