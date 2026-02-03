open Caml_light

type linear_element =
  | Variable of variable node
  | Constant of constant node
  | Parenthesised of { inner : linear_form; style : parenthesis_style }
  | TypeCoercion of { inner : linear_form; typ : type_expression node }
  | ListLiteral of linear_form list
  | ArrayLiteral of linear_form list
  | RecordLiteral of (label node * linear_form) list
  | WhileLoop of { condition : linear_form; body : linear_form }
  | ForLoop of {
      direction : for_direction;
      variable : lowercase_ident node;
      start : linear_form;
      finish : linear_form;
      body : linear_form;
    }
  | Dereference of linear_form
  | FieldAccess of { receiver : linear_form; target : label node }
  | ArrayAccess of { receiver : linear_form; target : linear_form }
  | FunctionApplication of {
      receiver : linear_form;
      arguments : linear_form list;
    }
  | PrefixOperation of { receiver : linear_form; operation : prefix_operation }
  | InfixOperation of {
      lhs : linear_form;
      rhs : linear_form;
      operation : infix_operation;
    }
  | Negation of linear_form
  | Tuple of linear_form list
  | FieldAssignment of {
      receiver : linear_form;
      target : label node;
      value : linear_form;
    }
  | ArrayAssignment of {
      receiver : linear_form;
      target : linear_form;
      value : linear_form;
    }
  | ReferenceAssignment of { receiver : linear_form; value : linear_form }
  | If of {
      condition : linear_form;
      body : linear_form;
      else_body : linear_form option;
    }
  | Sequence of linear_form list
  | Match of { value : linear_form; cases : linear_pattern_cases }
  | Try of { value : linear_form; cases : linear_pattern_cases }
  | FunctionLiteral of linear_function_literal
  | LetBinding of {
      bindings : linear_binding node list;
      is_rec : bool;
      inner : linear_form;
    }
  | StringAccess of { receiver : linear_form; target : linear_form }
  | StringAssignment of {
      receiver : linear_form;
      target : linear_form;
      value : linear_form;
    }

and linear_pattern_cases = (pattern node list * linear_form) list

and linear_function_literal = {
  style : function_literal_style;
  cases : linear_pattern_cases;
}

and linear_function_ = {
  name : variable node;
  parameters : pattern node list;
  body : linear_form;
}

and linear_binding =
  | Variable of { lhs : pattern node; value : linear_form }
  | Function of linear_function_

and linear_form = (variable * linear_element) list

(** Given a linear form l, extracts the name associated with the last linear
    element in l *)
let rec last_var (l : linear_form) : variable =
  match l with
  | [] -> failwith "l was empty"
  | (p, _) :: [] -> p
  | x :: q -> last_var q

(** Converts an OCaml expression e to a linear form, associating the generated
    linear elements with the names a_k, a_(k+1), and so on.

    Returns the linear form and the index after the last used name. *)
let rec linearize (e : expression) (k : int) : linear_form * int =
  let p (i : int) : variable = "a_" ^ string_of_int i in

  match e with
  | Variable v -> ([ (p k, Variable v) ], k + 1)
  | Constant c -> ([ (p k, Constant c) ], k + 1)
  | Parenthesised { inner; style } -> linearize inner k
  | TypeCoercion { inner; typ } ->
      let inner_lin, k = linearize inner k in
      let inner_var = last_var inner_lin in
      let e_elt =
        TypeCoercion { inner = [ (p (k + 1), Variable inner_var) ]; typ }
      in
      (inner_lin @ [ (p k, e_elt) ], k + 2)
  | ListLiteral l ->
      let elt_lins, elt_names, k =
        List.fold_left
          (fun (lins, names, k) elt ->
            let elt_lin, k = linearize elt k in
            let elt_name = last_var elt_lin in
            (elt_lin :: lins, elt_name :: names, k))
          ([], [], k) l
      in
      let e_elt =
        ListLiteral
          (elt_names |> List.rev
          |> List.mapi (fun i name -> [ (p (k + i + 1), Variable name) ]))
      in
      let elt_count = List.length elt_names in
      ( (elt_lins |> List.rev |> List.concat) @ [ (p k, e_elt) ],
        k + elt_count + 1 )
  | ArrayLiteral l ->
      let elt_lins, elt_names, k =
        List.fold_left
          (fun (lins, names, k) elt ->
            let elt_lin, k = linearize elt k in
            let elt_name = last_var elt_lin in
            (elt_lin :: lins, elt_name :: names, k))
          ([], [], k) l
      in
      let e_elt =
        ArrayLiteral
          (elt_names |> List.rev
          |> List.mapi (fun i name -> [ (p (k + i + 1), Variable name) ]))
      in
      let elt_count = List.length elt_names in
      ( (elt_lins |> List.rev |> List.concat) @ [ (p k, e_elt) ],
        k + elt_count + 1 )
  | RecordLiteral l ->
      let elt_lins, elt_names, k =
        List.fold_left
          (fun (lins, names, k) (field, elt) ->
            let elt_lin, k = linearize elt k in
            let elt_name = last_var elt_lin in
            (elt_lin :: lins, (field, elt_name) :: names, k))
          ([], [], k) l
      in
      let e_elt =
        RecordLiteral
          (elt_names |> List.rev
          |> List.mapi (fun i (field, name) ->
                 (field, [ (p (k + i + 1), Variable name) ])))
      in
      let elt_count = List.length elt_names in
      ( (elt_lins |> List.rev |> List.concat) @ [ (p k, e_elt) ],
        k + elt_count + 1 )
  | WhileLoop _ -> failwith "Cannot linearize while loops"
  | ForLoop _ -> failwith "Cannot linearize for loops"
  | Dereference inner ->
      let inner_lin, k = linearize inner k in
      let inner_var = last_var inner_lin in
      let e_elt = Dereference [ (p (k + 1), Variable inner_var) ] in
      (inner_lin @ [ (p k, e_elt) ], k + 2)
  | FieldAccess { target; receiver } -> (
      match receiver with
      | Constant c ->
          (* This is a module access *)
          ( [
              ( p k,
                FieldAccess { receiver = [ (p (k + 1), Constant c) ]; target }
              );
            ],
            k + 2 )
      | _ ->
          let receiver_lin, k = linearize receiver k in
          let receiver_var = last_var receiver_lin in
          let e_elt =
            FieldAccess
              { target; receiver = [ (p (k + 1), Variable receiver_var) ] }
          in
          (receiver_lin @ [ (p k, e_elt) ], k + 2))
  | ArrayAccess { target; receiver } ->
      let receiver_lin, k = linearize receiver k in
      let receiver_var = last_var receiver_lin in
      let target_lin, k = linearize target k in
      let target_var = last_var target_lin in
      let e_elt =
        ArrayAccess
          {
            receiver = [ (p (k + 1), Variable receiver_var) ];
            target = [ (p (k + 2), Variable target_var) ];
          }
      in
      (receiver_lin @ target_lin @ [ (p k, e_elt) ], k + 3)
  | FunctionApplication { receiver; arguments } -> (
      match receiver with
      | Constant c ->
          (* This is a type constructor. Technically we deviate from the definition of a correct
          linear form here (the argument may be a parenthesised tuple with depth > 1). *)
          let arguments_lins, argument_names, k =
            match arguments with
            | [ Parenthesised { inner = Tuple actual_arguments } ] ->
                List.fold_left
                  (fun (lins, names, k) elt ->
                    let elt_lin, k = linearize elt k in
                    let elt_name = last_var elt_lin in
                    (elt_lin :: lins, elt_name :: names, k))
                  ([], [], k) actual_arguments
            | [ argument ] ->
                let argument_lin, k = linearize argument k in
                let argument_name = last_var argument_lin in
                ([ argument_lin ], [ argument_name ], k)
            | _ -> failwith "Type constructor had more than one argument"
          in
          let e_elt =
            match argument_names with
            | [ argument ] ->
                FunctionApplication
                  {
                    receiver = [ (p (k + 1), Constant c) ];
                    arguments = [ [ (p (k + 2), Variable argument) ] ];
                  }
            | _ ->
                FunctionApplication
                  {
                    receiver = [ (p (k + 1), Constant c) ];
                    arguments =
                      [
                        [
                          ( p (k + 2),
                            Parenthesised
                              {
                                style = Parenthesis;
                                inner =
                                  [
                                    ( p (k + 3),
                                      Tuple
                                        (argument_names |> List.rev
                                        |> List.mapi (fun i arg ->
                                               [ (p (k + i + 4), Variable arg) ])
                                        ) );
                                  ];
                              } );
                        ];
                      ];
                  }
          in
          let argument_count = List.length argument_names in
          ( (arguments_lins |> List.rev |> List.concat) @ [ (p k, e_elt) ],
            k + argument_count + 4 )
      | _ ->
          let receiver_lin, k = linearize receiver k in
          let receiver_var = last_var receiver_lin in
          let arg_lins, arg_names, k =
            List.fold_left
              (fun (lins, names, k) elt ->
                let elt_lin, k = linearize elt k in
                let elt_name = last_var elt_lin in
                (elt_lin :: lins, elt_name :: names, k))
              ([], [], k) arguments
          in
          let e_elt =
            FunctionApplication
              {
                receiver = [ (p (k + 1), Variable receiver_var) ];
                arguments =
                  arg_names |> List.rev
                  |> List.mapi (fun i name ->
                         [ (p (k + i + 2), Variable name) ]);
              }
          in
          let argument_count = List.length arguments in
          ( receiver_lin
            @ (arg_lins |> List.rev |> List.concat)
            @ [ (p k, e_elt) ],
            k + argument_count + 2 ))
  | PrefixOperation { operation; receiver } ->
      let receiver_lin, k = linearize receiver k in
      let receiver_var = last_var receiver_lin in
      let e_elt =
        PrefixOperation
          { operation; receiver = [ (p (k + 1), Variable receiver_var) ] }
      in
      (receiver_lin @ [ (p k, e_elt) ], k + 2)
  | InfixOperation { lhs; rhs; operation } ->
      let lhs_lin, k = linearize lhs k in
      let lhs_var = last_var lhs_lin in
      let rhs_lin, k = linearize rhs k in
      let rhs_var = last_var rhs_lin in
      let e_elt =
        InfixOperation
          {
            operation;
            lhs = [ (p (k + 1), Variable lhs_var) ];
            rhs = [ (p (k + 2), Variable rhs_var) ];
          }
      in
      (lhs_lin @ rhs_lin @ [ (p k, e_elt) ], k + 3)
  | Negation inner ->
      let inner_lin, k = linearize inner k in
      let inner_var = last_var inner_lin in
      let e_elt = Negation [ (p (k + 1), Variable inner_var) ] in
      (inner_lin @ [ (p k, e_elt) ], k + 2)
  | Tuple t ->
      let elt_lins, elt_names, k =
        List.fold_left
          (fun (lins, names, k) elt ->
            let elt_lin, k = linearize elt k in
            let elt_name = last_var elt_lin in
            (elt_lin :: lins, elt_name :: names, k))
          ([], [], k) t
      in
      let e_elt =
        Tuple
          (elt_names |> List.rev
          |> List.mapi (fun i name -> [ (p (k + i + 1), Variable name) ]))
      in
      let elt_count = List.length elt_names in
      ( (elt_lins |> List.rev |> List.concat) @ [ (p k, e_elt) ],
        k + elt_count + 1 )
  | FieldAssignment { receiver; target; value } ->
      let receiver_lin, k = linearize receiver k in
      let receiver_var = last_var receiver_lin in
      let value_lin, k = linearize value k in
      let value_var = last_var value_lin in
      let e_elt =
        FieldAssignment
          {
            receiver = [ (p (k + 1), Variable receiver_var) ];
            target;
            value = [ (p (k + 2), Variable value_var) ];
          }
      in
      (receiver_lin @ value_lin @ [ (p k, e_elt) ], k + 3)
  | ArrayAssignment { receiver; target; value } ->
      let receiver_lin, k = linearize receiver k in
      let receiver_var = last_var receiver_lin in
      let target_lin, k = linearize target k in
      let target_var = last_var target_lin in
      let value_lin, k = linearize value k in
      let value_var = last_var value_lin in
      let e_elt =
        ArrayAssignment
          {
            receiver = [ (p (k + 1), Variable receiver_var) ];
            target = [ (p (k + 2), Variable target_var) ];
            value = [ (p (k + 3), Variable value_var) ];
          }
      in
      (receiver_lin @ target_lin @ value_lin @ [ (p k, e_elt) ], k + 4)
  | ReferenceAssignment { receiver; value } ->
      let receiver_lin, k = linearize receiver k in
      let receiver_var = last_var receiver_lin in
      let value_lin, k = linearize value k in
      let value_var = last_var value_lin in
      let e_elt =
        ReferenceAssignment
          {
            receiver = [ (p (k + 1), Variable receiver_var) ];
            value = [ (p (k + 2), Variable value_var) ];
          }
      in
      (receiver_lin @ value_lin @ [ (p k, e_elt) ], k + 3)
  | If { condition; body; else_body } ->
      let condition_lin, k = linearize condition k in
      let condition_var = last_var condition_lin in
      let body_lin, k = linearize body k in
      let else_body_lin, k =
        match else_body with
        | None -> (None, k)
        | Some else_body ->
            let else_body_lin, k = linearize else_body k in
            (Some else_body_lin, k)
      in
      let e_elt =
        If
          {
            condition = [ (p (k + 2), Variable condition_var) ];
            body = body_lin;
            else_body = else_body_lin;
          }
      in
      (condition_lin @ [ (p k, e_elt) ], k + 3)
  | Sequence s ->
      let elt_lins, k =
        List.fold_left
          (fun (lins, k) elt ->
            let elt_lin, k = linearize elt k in
            (elt_lin :: lins, k))
          ([], k) s
      in
      (elt_lins |> List.rev |> List.concat, k)
  | Match { value; cases } ->
      let value_lin, k = linearize value k in
      let value_var = last_var value_lin in
      let orig_k = k in
      let cases_lins, k =
        List.fold_left
          (fun (lins, k) (pattern, body) ->
            let body_lin, k = linearize body k in
            ((pattern, body_lin) :: lins, k))
          ([], orig_k + 2)
          cases
      in
      let e_elt =
        Match
          {
            value = [ (p (orig_k + 1), Variable value_var) ];
            cases = List.rev cases_lins;
          }
      in
      (value_lin @ [ (p orig_k, e_elt) ], k)
  | Try _ -> failwith "Cannot linearize try expressions"
  | FunctionLiteral { style; cases } ->
      let orig_k = k in
      let cases_lins, k =
        List.fold_left
          (fun (lins, k) (pattern, body) ->
            let body_lin, k = linearize body k in
            ((pattern, body_lin) :: lins, k))
          ([], orig_k + 1)
          cases
      in
      let e_elt = FunctionLiteral { style; cases = List.rev cases_lins } in
      ([ (p orig_k, e_elt) ], k)
  | LetBinding { bindings; is_rec; inner } ->
      let bindings_as_assignments =
        bindings
        |> List.map (fun (binding : Caml_light.binding) ->
               match binding with
               | Function { name; parameters; body } ->
                   ( Ident name,
                     Caml_light.FunctionLiteral
                       { style = Fun; cases = [ (parameters, body) ] } )
               | Variable { lhs; value } -> (lhs, value))
      in
      let bindings_lins, k =
        List.fold_left
          (fun (lins, k) (lhs, elt) ->
            let elt_lin, k = linearize elt k in
            (elt_lin :: lins, k))
          ([], k) bindings_as_assignments
      in
      let inner_lin, k = linearize inner k in
      let e_elt =
        LetBinding
          {
            bindings =
              bindings_lins |> List.rev
              |> List.mapi (fun i elt_lin ->
                     let corresponding_pattern =
                       fst (List.nth bindings_as_assignments i)
                     in
                     (Variable
                        {
                          lhs = corresponding_pattern;
                          value = [ (p (k + i), Variable (last_var elt_lin)) ];
                        }
                       : linear_binding));
            is_rec = false;
            inner = inner_lin;
          }
      in
      ( [ (p (k + List.length bindings_lins), e_elt) ] :: bindings_lins
        |> List.rev |> List.concat,
        k + List.length bindings_lins + 1 )
  | StringAccess { target; receiver } ->
      let receiver_lin, k = linearize receiver k in
      let receiver_var = last_var receiver_lin in
      let target_lin, k = linearize target k in
      let target_var = last_var target_lin in
      let e_elt =
        ArrayAccess
          {
            receiver = [ (p (k + 1), Variable receiver_var) ];
            target = [ (p (k + 2), Variable target_var) ];
          }
      in
      (receiver_lin @ target_lin @ [ (p k, e_elt) ], k + 3)
  | StringAssignment { receiver; target; value } ->
      let receiver_lin, k = linearize receiver k in
      let receiver_var = last_var receiver_lin in
      let target_lin, k = linearize target k in
      let target_var = last_var target_lin in
      let value_lin, k = linearize value k in
      let value_var = last_var value_lin in
      let e_elt =
        ArrayAssignment
          {
            receiver = [ (p (k + 1), Variable receiver_var) ];
            target = [ (p (k + 2), Variable target_var) ];
            value = [ (p (k + 3), Variable value_var) ];
          }
      in
      (receiver_lin @ target_lin @ value_lin @ [ (p k, e_elt) ], k + 4)

let rec element_contains_reference (f : variable) (e : linear_element) : bool =
  match e with
  | Variable v -> v == f
  | Constant _ -> false
  | Parenthesised { inner } | TypeCoercion { inner } ->
      contains_reference f inner
  | ListLiteral l | ArrayLiteral l -> List.exists (contains_reference f) l
  | RecordLiteral l -> l |> List.map snd |> List.exists (contains_reference f)
  | WhileLoop _ -> failwith "Found linearized while loop"
  | ForLoop _ -> failwith "Found linearized for loop"
  | Dereference inner -> contains_reference f inner
  | FieldAccess { receiver } -> contains_reference f receiver
  | ArrayAccess { receiver; target } ->
      contains_reference f receiver || contains_reference f target
  | FunctionApplication { receiver; arguments } ->
      contains_reference f receiver
      || List.exists (contains_reference f) arguments
  | PrefixOperation { receiver } -> contains_reference f receiver
  | InfixOperation { lhs; rhs } ->
      contains_reference f lhs || contains_reference f rhs
  | Negation inner -> contains_reference f inner
  | Tuple l -> List.exists (contains_reference f) l
  | FieldAssignment { receiver; value } ->
      contains_reference f receiver || contains_reference f value
  | ArrayAssignment { receiver; target; value } ->
      contains_reference f receiver
      || contains_reference f target
      || contains_reference f value
  | ReferenceAssignment { receiver; value } ->
      contains_reference f receiver || contains_reference f value
  | If { condition; body; else_body } -> (
      contains_reference f condition
      || contains_reference f body
      || match else_body with None -> false | Some b -> contains_reference f b)
  | Sequence s -> List.exists (contains_reference f) s
  | Match { value; cases } ->
      contains_reference f value
      || cases |> List.map snd |> List.exists (contains_reference f)
  | Try _ -> failwith "Found linearized try"
  | FunctionLiteral { cases } ->
      List.exists (fun (_, body) -> contains_reference f body) cases
  | LetBinding { bindings; inner } ->
      contains_reference f inner
      || bindings
         |> List.exists (fun (binding : linear_binding) ->
                match binding with
                | Variable { value } -> contains_reference f value
                | Function { body } -> contains_reference f body)
  | StringAccess { receiver; target } ->
      contains_reference f receiver || contains_reference f target
  | StringAssignment { receiver; target; value } ->
      contains_reference f receiver
      || contains_reference f target
      || contains_reference f value

(** contains_reference f l is true iff l contains `Variable f` *)
and contains_reference (f : variable) (l : linear_form) : bool =
  match l with
  | [] -> false
  | (p, e) :: q -> element_contains_reference f e || contains_reference f q

let rec delinearize_element (e : linear_element) (prev_vars : linear_form) :
    expression * variable list =
  match e with
  | Variable v -> (
      match List.assoc_opt v prev_vars with
      | None -> (Variable v, [])
      | Some definition ->
          let inlined_elt, inlined_vars =
            delinearize_element definition
              (List.filter (fun (name, _) -> name <> v) prev_vars)
          in
          ( Parenthesised { inner = inlined_elt; style = Parenthesis },
            v :: inlined_vars ))
  | Constant c -> (Constant c, [])
  | Parenthesised { style; inner } ->
      let inner_inlined, inlined_vars = delinearize inner prev_vars in
      (Parenthesised { style; inner = inner_inlined }, inlined_vars)
  | TypeCoercion { typ; inner } ->
      let inner_inlined, inlined_vars = delinearize inner prev_vars in
      (TypeCoercion { typ; inner = inner_inlined }, inlined_vars)
  | ListLiteral l ->
      let terms, inlined_vars =
        List.fold_right
          (fun elt (terms, inlined_vars) ->
            let elt_inlined, inlined_vars' = delinearize elt prev_vars in
            (elt_inlined :: terms, inlined_vars' @ inlined_vars))
          l ([], [])
      in

      (ListLiteral terms, inlined_vars)
  | ArrayLiteral l ->
      let terms, inlined_vars =
        List.fold_right
          (fun elt (terms, inlined_vars) ->
            let elt_inlined, inlined_vars' = delinearize elt prev_vars in
            (elt_inlined :: terms, inlined_vars' @ inlined_vars))
          l ([], [])
      in

      (ArrayLiteral terms, inlined_vars)
  | RecordLiteral l ->
      let terms, inlined_vars =
        List.fold_right
          (fun (name, elt) (terms, inlined_vars) ->
            let elt_inlined, inlined_vars' = delinearize elt prev_vars in
            ((name, elt_inlined) :: terms, inlined_vars' @ inlined_vars))
          l ([], [])
      in

      (RecordLiteral terms, inlined_vars)
  | WhileLoop _ -> failwith "Found linearized while loop"
  | ForLoop _ -> failwith "Found linearized for loop"
  | Dereference inner ->
      let inner_inlined, inlined_vars = delinearize inner prev_vars in
      (Dereference inner_inlined, inlined_vars)
  | FieldAccess { receiver; target } ->
      let receiver_inlined, inlined_vars = delinearize receiver prev_vars in
      (FieldAccess { receiver = receiver_inlined; target }, inlined_vars)
  | ArrayAccess { receiver; target } ->
      let receiver_inlined, inlined_vars = delinearize receiver prev_vars in
      let target_inlined, inlined_vars_2 = delinearize receiver prev_vars in
      ( ArrayAccess { receiver = receiver_inlined; target = target_inlined },
        inlined_vars @ inlined_vars_2 )
  | FunctionApplication { receiver; arguments } ->
      let receiver_inlined, inlined_vars = delinearize receiver prev_vars in
      let arguments_inlined, inlined_vars_2 =
        List.fold_right
          (fun elt (terms, inlined_vars) ->
            let elt_inlined, inlined_vars' = delinearize elt prev_vars in
            (elt_inlined :: terms, inlined_vars' @ inlined_vars))
          arguments ([], [])
      in
      ( FunctionApplication
          { receiver = receiver_inlined; arguments = arguments_inlined },
        inlined_vars @ inlined_vars_2 )
  | PrefixOperation { operation; receiver } ->
      let receiver_inlined, inlined_vars = delinearize receiver prev_vars in
      (PrefixOperation { operation; receiver = receiver_inlined }, inlined_vars)
  | InfixOperation { lhs; operation; rhs } ->
      let lhs_inlined, inlined_vars = delinearize lhs prev_vars in
      let rhs_inlined, inlined_vars2 = delinearize rhs prev_vars in
      ( InfixOperation { lhs = lhs_inlined; operation; rhs = rhs_inlined },
        inlined_vars @ inlined_vars2 )
  | Negation inner ->
      let inner_inlined, inlined_vars = delinearize inner prev_vars in
      (Negation inner_inlined, inlined_vars)
  | Tuple l ->
      let terms, inlined_vars =
        List.fold_right
          (fun elt (terms, inlined_vars) ->
            let elt_inlined, inlined_vars' = delinearize elt prev_vars in
            (elt_inlined :: terms, inlined_vars' @ inlined_vars))
          l ([], [])
      in

      (Tuple terms, inlined_vars)
  | FieldAssignment { receiver; target; value } ->
      let receiver_inlined, inlined_vars = delinearize receiver prev_vars in
      let value_inlined, inlined_vars_2 = delinearize value prev_vars in
      ( FieldAssignment
          { receiver = receiver_inlined; target; value = value_inlined },
        inlined_vars @ inlined_vars_2 )
  | ArrayAssignment { receiver; target; value } ->
      let receiver_inlined, inlined_vars = delinearize receiver prev_vars in
      let value_inlined, inlined_vars_2 = delinearize value prev_vars in
      let target_inlined, inlined_vars_3 = delinearize value prev_vars in
      ( ArrayAssignment
          {
            receiver = receiver_inlined;
            target = target_inlined;
            value = value_inlined;
          },
        inlined_vars @ inlined_vars_2 @ inlined_vars_3 )
  | ReferenceAssignment { receiver; value } ->
      let receiver_inlined, inlined_vars = delinearize receiver prev_vars in
      let value_inlined, inlined_vars_2 = delinearize value prev_vars in
      ( ReferenceAssignment
          { receiver = receiver_inlined; value = value_inlined },
        inlined_vars @ inlined_vars_2 )
  | If { condition; body; else_body } ->
      let condition_inlined, inlined_vars = delinearize condition prev_vars in
      let body_inlined, inlined_vars_2 = delinearize body prev_vars in
      let else_inlined, inlined_vars_3 =
        match else_body with
        | None -> (None, [])
        | Some b ->
            let b_inlined, inlined_vars = delinearize b prev_vars in
            (Some b_inlined, inlined_vars)
      in
      ( If
          {
            condition = condition_inlined;
            body = body_inlined;
            else_body = else_inlined;
          },
        inlined_vars @ inlined_vars_2 @ inlined_vars_3 )
  | Sequence s ->
      let terms, inlined_vars =
        List.fold_right
          (fun elt (terms, inlined_vars) ->
            let elt_inlined, inlined_vars' = delinearize elt prev_vars in
            (elt_inlined :: terms, inlined_vars' @ inlined_vars))
          s ([], [])
      in

      (Sequence terms, inlined_vars)
  | Match { value; cases } ->
      let value_inlined, inlined_vars = delinearize value prev_vars in
      let cases_inlined, inlined_vars_2 =
        List.fold_right
          (fun (pattern, elt) (terms, inlined_vars) ->
            let elt_inlined, inlined_vars' = delinearize elt prev_vars in
            ((pattern, elt_inlined) :: terms, inlined_vars' @ inlined_vars))
          cases ([], [])
      in

      ( Match { value = value_inlined; cases = cases_inlined },
        inlined_vars @ inlined_vars_2 )
  | Try _ -> failwith "Found linearized try"
  | FunctionLiteral { style; cases } ->
      let cases_inlined, inlined_vars =
        List.fold_right
          (fun (pattern, elt) (terms, inlined_vars) ->
            let elt_inlined, inlined_vars' = delinearize elt prev_vars in
            ((pattern, elt_inlined) :: terms, inlined_vars' @ inlined_vars))
          cases ([], [])
      in
      (FunctionLiteral { style; cases = cases_inlined }, inlined_vars)
  | LetBinding { bindings; is_rec; inner } ->
      let bindings_inlined, inlined_vars =
        List.fold_right
          (fun binding (terms, inlined_vars) ->
            match binding with
            | (Variable { lhs; value } : linear_binding) ->
                let value_inlined, inlined_vars' =
                  delinearize value prev_vars
                in
                ( (Variable { lhs; value = value_inlined } : binding) :: terms,
                  inlined_vars' @ inlined_vars )
            | Function { name; parameters; body } ->
                let body_inlined, inlined_vars' = delinearize body prev_vars in
                ( Function { name; parameters; body = body_inlined } :: terms,
                  inlined_vars' @ inlined_vars ))
          bindings ([], [])
      in
      let inner_inlined, inlined_vars_2 = delinearize inner prev_vars in
      ( LetBinding { bindings = bindings_inlined; is_rec; inner = inner_inlined },
        inlined_vars @ inlined_vars_2 )
  | StringAccess { receiver; target } ->
      let receiver_inlined, inlined_vars = delinearize receiver prev_vars in
      let target_inlined, inlined_vars_2 = delinearize receiver prev_vars in
      ( StringAccess { receiver = receiver_inlined; target = target_inlined },
        inlined_vars @ inlined_vars_2 )
  | StringAssignment { receiver; target; value } ->
      let receiver_inlined, inlined_vars = delinearize receiver prev_vars in
      let value_inlined, inlined_vars_2 = delinearize value prev_vars in
      let target_inlined, inlined_vars_3 = delinearize value prev_vars in
      ( StringAssignment
          {
            receiver = receiver_inlined;
            target = target_inlined;
            value = value_inlined;
          },
        inlined_vars @ inlined_vars_2 @ inlined_vars_3 )

(** delinearize l prev_vars converts a linear form l to an OCaml expression.

    In addition to the algorithm detailed in the paper, three additional
    modifications are performed to improve legibility:

    - Use of function bindings: Instead of generating bindings of the form `let
      x = fun arg1 ... argn -> body`, generate `let x arg1 ... argn = body`

    - Inlining: If a variable is encountered and prev_vars contains a definition
      for that variable, replace the occurrence of the variable with the
      definition. This helps to undo the "flattening" introduced by linearize.

    - Use of sequences: Instead of generating `let x = value in e`, if `x` does
      not appear in `e`, generate `value; e`.

    This function returns the generated expression as well as a list of
    variables that were inlined. *)
and delinearize (l : linear_form) (prev_vars : linear_form) :
    expression * variable list =
  match l with
  | [] -> failwith "Empty linear form"
  | (p, e) :: [] -> delinearize_element e prev_vars
  (* Special case for formatting functions nicely *)
  | (p, FunctionLiteral { style; cases = [ (args, body) ] }) :: q ->
      let q_inlined, inlined_vars = delinearize q prev_vars in
      let body_inlined, inlined_vars_2 = delinearize body prev_vars in
      ( LetBinding
          {
            is_rec = false;
            bindings =
              [ Function { name = p; parameters = args; body = body_inlined } ];
            inner = q_inlined;
          },
        inlined_vars @ inlined_vars_2 )
  | (p, e) :: q ->
      let q_delinearized, inlined_vars = delinearize q ((p, e) :: prev_vars) in
      if List.mem p inlined_vars then (q_delinearized, inlined_vars)
      else
        let e_inlined, inlined_vars_2 = delinearize_element e prev_vars in
        if contains_reference p q then
          ( LetBinding
              {
                is_rec = false;
                bindings = [ Variable { lhs = Ident p; value = e_inlined } ];
                inner = q_delinearized;
              },
            inlined_vars @ inlined_vars_2 )
        else
          ( Parenthesised
              {
                inner = Sequence [ e_inlined; q_delinearized ];
                style = Parenthesis;
              },
            inlined_vars @ inlined_vars_2 )

let rec element_contains_application (f : variable) (e : linear_element) : bool
    =
  match e with
  | Variable _ -> false
  | Constant _ -> false
  | Parenthesised { inner } | TypeCoercion { inner } ->
      contains_application f inner
  | ListLiteral l | ArrayLiteral l -> List.exists (contains_application f) l
  | RecordLiteral l -> l |> List.map snd |> List.exists (contains_application f)
  | WhileLoop _ -> failwith "Found linearized while loop"
  | ForLoop _ -> failwith "Found linearized for loop"
  | Dereference inner -> contains_application f inner
  | FieldAccess { receiver } -> contains_application f receiver
  | ArrayAccess { receiver; target } ->
      contains_application f receiver || contains_application f target
  | FunctionApplication { receiver; arguments } ->
      (match receiver with [ (_, Variable f') ] -> f' = f | _ -> false)
      || contains_application f receiver
      || List.exists (contains_application f) arguments
  | PrefixOperation { receiver } -> contains_application f receiver
  | InfixOperation { lhs; rhs } ->
      contains_application f lhs || contains_application f rhs
  | Negation inner -> contains_application f inner
  | Tuple l -> List.exists (contains_application f) l
  | FieldAssignment { receiver; value } ->
      contains_application f receiver || contains_application f value
  | ArrayAssignment { receiver; target; value } ->
      contains_application f receiver
      || contains_application f target
      || contains_application f value
  | ReferenceAssignment { receiver; value } ->
      contains_application f receiver || contains_application f value
  | If { condition; body; else_body } -> (
      contains_application f condition
      || contains_application f body
      ||
      match else_body with None -> false | Some b -> contains_application f b)
  | Sequence s -> List.exists (contains_application f) s
  | Match { value; cases } ->
      contains_application f value
      || cases |> List.map snd |> List.exists (contains_application f)
  | Try _ -> failwith "Found linearized try"
  | FunctionLiteral { cases } ->
      List.exists (fun (_, body) -> contains_application f body) cases
  | LetBinding { bindings; inner } ->
      contains_application f inner
      || bindings
         |> List.exists (fun (binding : linear_binding) ->
                match binding with
                | Variable { value } -> contains_application f value
                | Function { body } -> contains_application f body)
  | StringAccess { receiver; target } ->
      contains_application f receiver || contains_application f target
  | StringAssignment { receiver; target; value } ->
      contains_application f receiver
      || contains_application f target
      || contains_application f value

(** contains_application f l is true iff l contains a FunctionApplication whose
    receiver is f *)
and contains_application (f : variable) (l : linear_form) : bool =
  match l with
  | [] -> false
  | (p, e) :: q -> element_contains_application f e || contains_application f q

(** map_locally_terminal_children applies a transformation only to the locally
    terminal children of f *)
let map_locally_terminal_children (f : linear_form -> linear_form)
    (e : linear_element) : linear_element =
  match (e : linear_element) with
  | If { condition; body; else_body } ->
      If
        {
          condition;
          body = f body;
          else_body =
            (match else_body with None -> None | Some b -> Some (f b));
        }
  | Match { value; cases } ->
      Match
        {
          value;
          cases = List.map (fun (pattern, body) -> (pattern, f body)) cases;
        }
  | LetBinding { is_rec; bindings; inner } ->
      LetBinding { is_rec; bindings; inner = f inner }
  (* No locally terminal children *)
  | _ -> e

(** rectify l c returns a linear form equivalent to l in which all calls to
    functions in c are made terminal.

    The functions in c are assumed to be later redefined to use CPS taking a
    continuation as their last argument. The bodies of any such functions
    defined within l are modified accordingly, but the function header is not.
*)
let rec rectify (l : linear_form) (cloture_rect : variable list) : linear_form =
  let rec find_first_recursive_element (tail : linear_form) (head : linear_form)
      : linear_form * ((variable * linear_element) * linear_form) option =
    match tail with
    | [] -> (List.rev head, None)
    | (p, e) :: q ->
        if List.exists (fun f -> element_contains_application f e) cloture_rect
        then (List.rev head, Some ((p, e), q))
        else find_first_recursive_element q ((p, e) :: head)
  in
  let l_1, maybe_recursive = find_first_recursive_element l [] in
  match maybe_recursive with
  | None ->
      let head_var = last_var l_1 in
      l_1
      @ [
          ( "cont_res",
            FunctionApplication
              {
                receiver = [ ("cont_call", Variable "cont") ];
                arguments = [ [ ("cont_arg", Variable head_var) ] ];
              } );
        ]
  | Some ((a, e), l_2) -> (
      match l_2 with
      | [] ->
          let e_rec =
            match e with
            | FunctionApplication { receiver = [ (p, Variable f) ]; arguments }
              when List.mem f cloture_rect ->
                FunctionApplication
                  {
                    receiver = [ (p, Variable f) ];
                    arguments =
                      arguments @ [ [ ("cont_arg", Variable "cont") ] ];
                  }
            | FunctionLiteral { style; cases } ->
                FunctionLiteral
                  {
                    style;
                    cases =
                      List.map
                        (fun (patterns, body) ->
                          ( patterns @ [ Ident "cont" ],
                            rectify body cloture_rect ))
                        cases;
                  }
            | _ ->
                map_locally_terminal_children
                  (fun f -> rectify f cloture_rect)
                  e
          in
          l_1 @ [ (a, e_rec) ]
      | _ ->
          let l_2_rec = rectify l_2 cloture_rect in
          let e_rec =
            match e with
            | FunctionApplication { receiver = [ (p, Variable f) ]; arguments }
              when List.mem f cloture_rect ->
                FunctionApplication
                  {
                    receiver = [ (p, Variable f) ];
                    arguments =
                      arguments @ [ [ ("cont_arg", Variable "cont") ] ];
                  }
            | FunctionLiteral { style; cases } ->
                FunctionLiteral
                  {
                    style;
                    cases =
                      List.map
                        (fun (patterns, body) ->
                          ( patterns @ [ Ident "cont" ],
                            rectify body cloture_rect ))
                        cases;
                  }
            | _ ->
                map_locally_terminal_children
                  (fun f -> rectify f cloture_rect)
                  e
          in
          l_1
          @ [
              ( "new_cont",
                FunctionLiteral
                  { style = Fun; cases = [ ([ Ident a ], l_2_rec) ] } );
              ("cont", Variable "new_cont");
              (a, e_rec);
            ])

let rec rename_elements_in (e : linear_element) (cloture_rect : variable list)
    (new_name : variable -> variable) =
  match e with
  | Variable v ->
      if List.mem v cloture_rect then Variable (new_name v) else Variable v
  | Constant _ -> e
  | Parenthesised { inner; style } ->
      Parenthesised
        { style; inner = rename_elements inner cloture_rect new_name }
  | TypeCoercion { inner; typ } ->
      TypeCoercion { inner = rename_elements inner cloture_rect new_name; typ }
  | ListLiteral l ->
      ListLiteral
        (List.map (fun l -> rename_elements l cloture_rect new_name) l)
  | ArrayLiteral l ->
      ArrayLiteral
        (List.map (fun l -> rename_elements l cloture_rect new_name) l)
  | RecordLiteral r ->
      RecordLiteral
        (List.map
           (fun (n, e) -> (n, rename_elements e cloture_rect new_name))
           r)
  | WhileLoop { condition; body } ->
      WhileLoop
        {
          condition = rename_elements condition cloture_rect new_name;
          body = rename_elements body cloture_rect new_name;
        }
  | ForLoop { direction = direction'; variable; start; finish; body } ->
      ForLoop
        {
          direction = direction';
          variable;
          start = rename_elements start cloture_rect new_name;
          finish = rename_elements finish cloture_rect new_name;
          body = rename_elements body cloture_rect new_name;
        }
  | Dereference e -> Dereference (rename_elements e cloture_rect new_name)
  | FieldAccess { receiver; target } ->
      FieldAccess
        { receiver = rename_elements receiver cloture_rect new_name; target }
  | ArrayAccess { receiver; target } ->
      ArrayAccess
        {
          receiver = rename_elements receiver cloture_rect new_name;
          target = rename_elements target cloture_rect new_name;
        }
  | FunctionApplication { receiver; arguments } ->
      FunctionApplication
        {
          receiver = rename_elements receiver cloture_rect new_name;
          arguments =
            List.map
              (fun arg -> rename_elements arg cloture_rect new_name)
              arguments;
        }
  | PrefixOperation { receiver; operation } ->
      PrefixOperation
        { operation; receiver = rename_elements receiver cloture_rect new_name }
  | InfixOperation { lhs; rhs; operation } ->
      InfixOperation
        {
          lhs = rename_elements lhs cloture_rect new_name;
          rhs = rename_elements rhs cloture_rect new_name;
          operation;
        }
  | Negation e -> Negation (rename_elements e cloture_rect new_name)
  | Tuple t ->
      Tuple (List.map (fun l -> rename_elements l cloture_rect new_name) t)
  | FieldAssignment { receiver; target; value } ->
      FieldAssignment
        {
          receiver = rename_elements receiver cloture_rect new_name;
          target;
          value = rename_elements value cloture_rect new_name;
        }
  | ArrayAssignment { receiver; target; value } ->
      ArrayAssignment
        {
          receiver = rename_elements receiver cloture_rect new_name;
          target = rename_elements target cloture_rect new_name;
          value = rename_elements value cloture_rect new_name;
        }
  | ReferenceAssignment { receiver; value } ->
      ReferenceAssignment
        {
          receiver = rename_elements receiver cloture_rect new_name;
          value = rename_elements value cloture_rect new_name;
        }
  | If { condition; body; else_body } ->
      If
        {
          condition = rename_elements condition cloture_rect new_name;
          body = rename_elements body cloture_rect new_name;
          else_body =
            Option.map
              (fun b -> rename_elements b cloture_rect new_name)
              else_body;
        }
  | Sequence s ->
      Sequence (List.map (fun e -> rename_elements e cloture_rect new_name) s)
  | Match { value; cases } ->
      Match
        {
          value = rename_elements value cloture_rect new_name;
          cases =
            List.map
              (fun (patterns, e) ->
                (patterns, rename_elements e cloture_rect new_name))
              cases;
        }
  | Try { value; cases } ->
      Try
        {
          value = rename_elements value cloture_rect new_name;
          cases =
            List.map
              (fun (patterns, e) ->
                (patterns, rename_elements e cloture_rect new_name))
              cases;
        }
  | FunctionLiteral { style; cases } ->
      FunctionLiteral
        {
          style;
          cases =
            List.map
              (fun (patterns, e) ->
                (patterns, rename_elements e cloture_rect new_name))
              cases;
        }
  | LetBinding { bindings; is_rec; inner } ->
      LetBinding
        {
          bindings =
            List.map
              (fun (binding : linear_binding) ->
                match binding with
                | Variable { lhs; value } ->
                    (Variable
                       {
                         lhs;
                         value = rename_elements value cloture_rect new_name;
                       }
                      : linear_binding)
                | Function { name; parameters; body } ->
                    Function
                      {
                        name;
                        parameters;
                        body = rename_elements body cloture_rect new_name;
                      })
              bindings;
          is_rec;
          inner = rename_elements inner cloture_rect new_name;
        }
  | StringAccess { receiver; target } ->
      StringAccess
        {
          receiver = rename_elements receiver cloture_rect new_name;
          target = rename_elements target cloture_rect new_name;
        }
  | StringAssignment { receiver; target; value } ->
      StringAssignment
        {
          receiver = rename_elements receiver cloture_rect new_name;
          target = rename_elements target cloture_rect new_name;
          value = rename_elements value cloture_rect new_name;
        }

(** rename_elements l c updates the definition and any references to variables
    in cloture_rect to their new names as indicated by new_name *)
and rename_elements (l : linear_form) (cloture_rect : variable list)
    (new_name : variable -> variable) =
  l
  |> List.map (fun (name, elt) ->
         let new_elt = rename_elements_in elt cloture_rect new_name in
         if List.mem name cloture_rect then (new_name name, new_elt)
         else (name, new_elt))

let rec find_definitions_in_element (fns : (variable * linear_element) list)
    (name : variable) (e : linear_element) : linear_element list =
  match e with
  | Variable _ | Constant _ -> []
  | Parenthesised { inner } | TypeCoercion { inner } | Dereference inner ->
      find_definitions fns name inner
  | ListLiteral l | ArrayLiteral l | Tuple l | Sequence l ->
      l |> List.map (fun elt -> find_definitions fns name elt) |> List.concat
  | RecordLiteral r ->
      r
      |> List.map (fun (_, elt) -> find_definitions fns name elt)
      |> List.concat
  | WhileLoop _ | ForLoop _ -> failwith "Found linearized loop"
  | FieldAccess { receiver } -> find_definitions fns name receiver
  | ArrayAccess { receiver; target } | StringAccess { receiver; target } ->
      find_definitions fns name receiver @ find_definitions fns name target
  | FunctionApplication { receiver; arguments } ->
      find_definitions fns name receiver
      @ (arguments
        |> List.map (fun arg -> find_definitions fns name arg)
        |> List.concat)
  | PrefixOperation { receiver } -> find_definitions fns name receiver
  | InfixOperation { lhs; rhs } ->
      find_definitions fns name lhs @ find_definitions fns name rhs
  | Negation receiver -> find_definitions fns name receiver
  | FieldAssignment { receiver; value } ->
      find_definitions fns name receiver @ find_definitions fns name value
  | ArrayAssignment { receiver; target; value }
  | StringAssignment { receiver; target; value } ->
      find_definitions fns name receiver
      @ find_definitions fns name target
      @ find_definitions fns name value
  | ReferenceAssignment { receiver; value } ->
      find_definitions fns name receiver @ find_definitions fns name value
  | If { condition; body; else_body } -> (
      find_definitions fns name condition
      @ find_definitions fns name body
      @
      match else_body with None -> [] | Some b -> find_definitions fns name b)
  | Match { value; cases } ->
      find_definitions fns name value
      @ (cases
        |> List.map (fun (_, body) -> find_definitions fns name body)
        |> List.concat)
  | Try _ -> failwith "Found linearized try"
  | FunctionLiteral { cases } ->
      List.map (fun (_, body) -> find_definitions fns name body) cases
      |> List.concat
  | LetBinding { bindings; inner } ->
      find_definitions fns name inner
      @ (bindings
        |> List.map (fun (binding : linear_binding) ->
               match binding with
               | Variable { value } -> find_definitions fns name value
               | Function { name; body } -> find_definitions fns name body)
        |> List.concat)

and find_definitions (fns : (variable * linear_element) list) (name : variable)
    (l : linear_form) : linear_element list =
  let child_definitions =
    l
    |> List.map (fun (_, e) -> find_definitions_in_element fns name e)
    |> List.flatten
  in
  let self_definitions =
    l
    |> List.filter_map (fun (variable, elt) ->
           if variable = name then Some elt else None)
  in

  child_definitions @ self_definitions

(** find_definition fns name finds the unique definition of the linear element
    with the name name in fns.

    Returns None if zero or multiple definitions are found. *)
and find_definition (fns : (variable * linear_element) list) (name : variable) :
    linear_element option =
  let root_definitions =
    fns
    |> List.filter_map (fun (name', def) ->
           if name' = name then Some def else None)
  in
  let inner_definitions =
    fns |> List.map snd
    |> List.map (find_definitions_in_element fns name)
    |> List.concat
  in
  let definitions = root_definitions @ inner_definitions in
  match definitions with [ def ] -> Some def | _ -> None

(** cloture_rectifiable fns computes a set that rectifies fns.

    Returns None if such a set could not be computed. *)
let cloture_rectifiable (fns : (variable * linear_element) list) :
    variable list option =
  let rec get_argument_count (fn : variable) : int option =
    match find_definition fns fn with
    | Some def -> (
        match def with
        | FunctionLiteral { cases } -> (
            match cases with
            | (arguments, _) :: _ -> Some (List.length arguments)
            | _ -> None)
        | Variable v -> get_argument_count v
        | _ -> None)
    | None -> None
  in

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
  in

  let rec get_nth_argument_names (fn : variable) (n : int) :
      variable list option =
    match find_definition fns fn with
    | Some def -> (
        match def with
        | FunctionLiteral { cases } ->
            let nth_names =
              List.map
                (fun (patterns, _) ->
                  let pattern = List.nth_opt patterns n in
                  match pattern with Some p -> get_name p | None -> None)
                cases
            in
            if List.for_all (fun name -> name <> None) nth_names then
              Some (nth_names |> List.map Option.get |> List.sort_uniq compare)
            else None
        | Variable v -> get_nth_argument_names v n
        | FunctionApplication { receiver; arguments } ->
            let receiver_name = last_var receiver in
            get_nth_argument_names receiver_name (n + List.length arguments)
        | _ -> None)
    | None -> None
  in

  let cloture = ref (fns |> List.map fst) in
  let a_traiter = ref !cloture in

  let add_fn (fn : variable) : unit =
    if not (List.mem fn !cloture) then (
      cloture := fn :: !cloture;
      a_traiter := fn :: !a_traiter)
  in

  let exception Exit in
  try
    while !a_traiter <> [] do
      let current = List.hd !a_traiter in
      a_traiter := List.tl !a_traiter;

      let current_argument_count =
        match get_argument_count current with Some n -> n | None -> raise Exit
      in

      let rec propagate_from_element (e_name : variable) (e : linear_element)
          (enclosing_function : variable) : unit =
        match e with
        | Variable _ | Constant _ -> ()
        | Parenthesised { inner } | TypeCoercion { inner } | Dereference inner
          ->
            propagate_from inner enclosing_function false
        | ListLiteral l | ArrayLiteral l | Tuple l | Sequence l ->
            l
            |> List.iter (fun elt ->
                   propagate_from elt enclosing_function false)
        | RecordLiteral r ->
            r
            |> List.iter (fun (_, elt) ->
                   propagate_from elt enclosing_function false)
        | WhileLoop _ | ForLoop _ -> failwith "Found linearized loop"
        | FieldAccess { receiver } ->
            propagate_from receiver enclosing_function false
        | ArrayAccess { receiver; target } | StringAccess { receiver; target }
          ->
            propagate_from receiver enclosing_function false;
            propagate_from target enclosing_function false
        | FunctionApplication { receiver; arguments } ->
            propagate_from receiver enclosing_function true;
            arguments
            |> List.iter (fun arg -> propagate_from arg enclosing_function true)
        | PrefixOperation { receiver } ->
            propagate_from receiver enclosing_function false
        | InfixOperation { lhs; rhs } ->
            propagate_from lhs enclosing_function false;
            propagate_from rhs enclosing_function false
        | Negation receiver -> propagate_from receiver enclosing_function false
        | FieldAssignment { receiver; value } ->
            propagate_from receiver enclosing_function false;
            propagate_from value enclosing_function false
        | ArrayAssignment { receiver; target; value }
        | StringAssignment { receiver; target; value } ->
            propagate_from receiver enclosing_function false;
            propagate_from target enclosing_function false;
            propagate_from value enclosing_function false
        | ReferenceAssignment { receiver; value } ->
            propagate_from receiver enclosing_function false;
            propagate_from value enclosing_function false
        | If { condition; body; else_body } -> (
            propagate_from condition enclosing_function false;
            propagate_from body enclosing_function false;
            match else_body with
            | None -> ()
            | Some b -> propagate_from b enclosing_function false)
        | Match { value; cases } ->
            propagate_from value enclosing_function false;
            cases
            |> List.iter (fun (_, body) ->
                   propagate_from body enclosing_function false)
        | Try _ -> failwith "Found linearized try"
        | FunctionLiteral { cases } ->
            List.iter (fun (_, body) -> propagate_from body e_name false) cases
        | LetBinding { bindings; inner } ->
            propagate_from inner enclosing_function false;
            bindings
            |> List.iter (fun (binding : linear_binding) ->
                   match binding with
                   | Variable { value } ->
                       propagate_from value enclosing_function false
                   | Function { name; body } -> propagate_from body name false)
      and propagate_from (l : linear_form) (enclosing_function : variable)
          (can_leak : bool) : unit =
        if last_var l = current && not can_leak then raise Exit;
        l
        |> List.iter (fun (name, element) ->
               match element with
               | Variable n -> if n = current then add_fn name
               | FunctionApplication { receiver; arguments } ->
                   let receiver = last_var receiver in
                   if receiver = current then
                     if List.length arguments = current_argument_count then
                       add_fn enclosing_function
                     else raise Exit
                   else
                     arguments
                     |> List.iteri (fun i argument ->
                            if last_var argument = current then
                              let ith_names =
                                get_nth_argument_names receiver i
                              in
                              match ith_names with
                              | Some names -> List.iter add_fn names
                              | None -> raise Exit)
               | _ -> ());

        l
        |> List.iter (fun (name, element) ->
               propagate_from_element name element enclosing_function)
      in

      fns
      |> List.iter (fun (name, def) ->
             propagate_from_element name def "UNKNOWN_GLOBAL_ENCLOSURE")
    done;
    Some !cloture
  with Exit -> None

(** find_continuations collects the definitions of all continuations defined in
    fns.

    The continuations are assumed to have been generated by `rectify`; that is,
    they are assumed to be named "new_cont". *)
let find_continuations (fns : (variable * linear_element) list)
    (cloture_rect : variable list) : linear_function_literal list option =
  let exception Exit in
  try
    let rec find_continuations_in_element (e : linear_element) :
        linear_function_literal list =
      match e with
      | Variable _ | Constant _ -> []
      | Parenthesised { inner } | TypeCoercion { inner } | Dereference inner ->
          find_continuations_in inner
      | ListLiteral l | ArrayLiteral l | Tuple l | Sequence l ->
          l |> List.map (fun elt -> find_continuations_in elt) |> List.concat
      | RecordLiteral r ->
          r
          |> List.map (fun (_, elt) -> find_continuations_in elt)
          |> List.concat
      | WhileLoop _ | ForLoop _ -> failwith "Found linearized loop"
      | FieldAccess { receiver } -> find_continuations_in receiver
      | ArrayAccess { receiver; target } | StringAccess { receiver; target } ->
          find_continuations_in receiver @ find_continuations_in target
      | FunctionApplication { receiver; arguments } ->
          find_continuations_in receiver
          @ (arguments
            |> List.map (fun arg -> find_continuations_in arg)
            |> List.concat)
      | PrefixOperation { receiver } -> find_continuations_in receiver
      | InfixOperation { lhs; rhs } ->
          find_continuations_in lhs @ find_continuations_in rhs
      | Negation receiver -> find_continuations_in receiver
      | FieldAssignment { receiver; value } ->
          find_continuations_in receiver @ find_continuations_in value
      | ArrayAssignment { receiver; target; value }
      | StringAssignment { receiver; target; value } ->
          find_continuations_in receiver
          @ find_continuations_in target
          @ find_continuations_in value
      | ReferenceAssignment { receiver; value } ->
          find_continuations_in receiver @ find_continuations_in value
      | If { condition; body; else_body } -> (
          find_continuations_in condition
          @ find_continuations_in body
          @
          match else_body with None -> [] | Some b -> find_continuations_in b)
      | Match { value; cases } ->
          find_continuations_in value
          @ (cases
            |> List.map (fun (_, body) -> find_continuations_in body)
            |> List.concat)
      | Try _ -> failwith "Found linearized try"
      | FunctionLiteral { cases } ->
          List.map (fun (_, body) -> find_continuations_in body) cases
          |> List.concat
      | LetBinding { bindings; inner } ->
          find_continuations_in inner
          @ (bindings
            |> List.map (fun (binding : linear_binding) ->
                   match binding with
                   | Variable { value } -> find_continuations_in value
                   | Function { name; body } -> find_continuations_in body)
            |> List.concat)
    and find_continuations_in (l : linear_form) : linear_function_literal list =
      match l with
      | [] -> []
      | (name, x) :: q ->
          let x_def =
            if name = "new_cont" then
              match x with
              | FunctionLiteral f -> [ f ]
              | _ -> failwith "Not a continuation, but named new_cont"
            else []
          in

          x_def @ find_continuations_in_element x @ find_continuations_in q
    in
    Some
      (List.fold_left
         (fun prev (name, body) -> prev @ find_continuations_in_element body)
         [] fns
      |> List.sort_uniq compare)
  with Exit -> None

(** find_initials fns returns the set of all values passed as base cases to the
    continuations of fns.

    Returns None if a base case was not a constant or if all base cases could
    not be computed. *)
let find_initials (fns : (variable * linear_element) list) :
    (variable list * constant list) option =
  let exception Exit in
  try
    let rec find_initials_in_element (e : linear_element) :
        (variable * constant) list =
      match e with
      | Variable _ | Constant _ -> []
      | Parenthesised { inner } | TypeCoercion { inner } | Dereference inner ->
          find_initials_in inner
      | ListLiteral l | ArrayLiteral l | Tuple l | Sequence l ->
          l |> List.map (fun elt -> find_initials_in elt) |> List.concat
      | RecordLiteral r ->
          r |> List.map (fun (_, elt) -> find_initials_in elt) |> List.concat
      | WhileLoop _ | ForLoop _ -> failwith "Found linearized loop"
      | FieldAccess { receiver } -> find_initials_in receiver
      | ArrayAccess { receiver; target } | StringAccess { receiver; target } ->
          find_initials_in receiver @ find_initials_in target
      | FunctionApplication { receiver; arguments } ->
          find_initials_in receiver
          @ (arguments
            |> List.map (fun arg -> find_initials_in arg)
            |> List.concat)
      | PrefixOperation { receiver } -> find_initials_in receiver
      | InfixOperation { lhs; rhs } ->
          find_initials_in lhs @ find_initials_in rhs
      | Negation receiver -> find_initials_in receiver
      | FieldAssignment { receiver; value } ->
          find_initials_in receiver @ find_initials_in value
      | ArrayAssignment { receiver; target; value }
      | StringAssignment { receiver; target; value } ->
          find_initials_in receiver @ find_initials_in target
          @ find_initials_in value
      | ReferenceAssignment { receiver; value } ->
          find_initials_in receiver @ find_initials_in value
      | If { condition; body; else_body } -> (
          find_initials_in condition @ find_initials_in body
          @ match else_body with None -> [] | Some b -> find_initials_in b)
      | Match { value; cases } ->
          find_initials_in value
          @ (cases
            |> List.map (fun (_, body) -> find_initials_in body)
            |> List.concat)
      | Try _ -> failwith "Found linearized try"
      | FunctionLiteral { cases } ->
          List.map (fun (_, body) -> find_initials_in body) cases |> List.concat
      | LetBinding { bindings; inner } ->
          find_initials_in inner
          @ (bindings
            |> List.map (fun (binding : linear_binding) ->
                   match binding with
                   | Variable { value } -> find_initials_in value
                   | Function { name; body } -> find_initials_in body)
            |> List.concat)
    and find_initials_in (l : linear_form) : (variable * constant) list =
      match l with
      | [] -> []
      | [
       ( _,
         FunctionApplication
           {
             receiver = [ (_, Variable "cont") ];
             arguments = [ [ (_, Variable arg) ] ];
           } );
      ] ->
          let rec find_constant_definition (arg : string) :
              (variable * constant) list =
            match find_definition fns arg with
            | Some (Variable v) ->
                let res = find_constant_definition v in
                (arg, snd (List.hd res)) :: res
            | Some (Constant c) -> [ (arg, c) ]
            | _ -> raise Exit
          in
          find_constant_definition arg
      | (name, x) :: q ->
          if name <> "new_cont" then
            find_initials_in_element x @ find_initials_in q
          else find_initials_in q
    in
    let pairs =
      List.fold_left
        (fun prev (name, body) -> prev @ find_initials_in_element body)
        [] fns
    in
    let names = List.map fst pairs in
    let constants = List.map snd pairs in

    Some (names, constants |> List.sort_uniq compare)
  with Exit -> None

(** Given a computation, if it is semantically the composition of a previous
    continuation with some new function, return that new function. Else return
    None.

    For example, the function `fun x -> if y then cont z else cont w` is
    semantically equivalent to `cont @@ (func x -> if y then z else w)`. *)
let extract_continuation_composition (cont : linear_function_literal) :
    linear_function_literal option =
  let exception NotSimple in
  let rec extract_without_continuation (l : linear_form) : linear_form =
    match l with
    | [] -> raise NotSimple
    | [
     ( _,
       FunctionApplication
         { receiver = [ (_, Variable "cont") ]; arguments = [ single_arg ] } );
    ] ->
        single_arg
    (* We ony get terminally recursive elements here *)
    | e :: q -> e :: extract_without_continuation q
  in
  try
    let res =
      {
        style = cont.style;
        cases =
          cont.cases
          |> List.map (fun (parameters, body) ->
                 (parameters, extract_without_continuation body));
      }
    in
    Some res
  with NotSimple -> None

(** Returns true iff all the functions of continuations commute. *)
let commutes (continuations : linear_function_literal list) : bool = true

let rec replace_element_continuations_with_accumulator (e : linear_element)
    (cloture_rect : variable list) (vars_to_replace : variable list) =
  match e with
  | Variable _ -> e
  | Constant _ -> e
  | Parenthesised { inner; style } ->
      Parenthesised
        {
          style;
          inner =
            replace_continuations_with_accumulator inner cloture_rect
              vars_to_replace;
        }
  | TypeCoercion { inner; typ } ->
      TypeCoercion
        {
          inner =
            replace_continuations_with_accumulator inner cloture_rect
              vars_to_replace;
          typ;
        }
  | ListLiteral l ->
      ListLiteral
        (List.map
           (fun l ->
             replace_continuations_with_accumulator l cloture_rect
               vars_to_replace)
           l)
  | ArrayLiteral l ->
      ArrayLiteral
        (List.map
           (fun l ->
             replace_continuations_with_accumulator l cloture_rect
               vars_to_replace)
           l)
  | RecordLiteral r ->
      RecordLiteral
        (List.map
           (fun (n, e) ->
             ( n,
               replace_continuations_with_accumulator e cloture_rect
                 vars_to_replace ))
           r)
  | WhileLoop { condition; body } ->
      WhileLoop
        {
          condition =
            replace_continuations_with_accumulator condition cloture_rect
              vars_to_replace;
          body =
            replace_continuations_with_accumulator body cloture_rect
              vars_to_replace;
        }
  | ForLoop { direction = direction'; variable; start; finish; body } ->
      ForLoop
        {
          direction = direction';
          variable;
          start =
            replace_continuations_with_accumulator start cloture_rect
              vars_to_replace;
          finish =
            replace_continuations_with_accumulator finish cloture_rect
              vars_to_replace;
          body =
            replace_continuations_with_accumulator body cloture_rect
              vars_to_replace;
        }
  | Dereference e ->
      Dereference
        (replace_continuations_with_accumulator e cloture_rect vars_to_replace)
  | FieldAccess { receiver; target } ->
      FieldAccess
        {
          receiver =
            replace_continuations_with_accumulator receiver cloture_rect
              vars_to_replace;
          target;
        }
  | ArrayAccess { receiver; target } ->
      ArrayAccess
        {
          receiver =
            replace_continuations_with_accumulator receiver cloture_rect
              vars_to_replace;
          target =
            replace_continuations_with_accumulator target cloture_rect
              vars_to_replace;
        }
  | FunctionApplication { receiver = [ (_, Variable "cont") ] } ->
      Variable "acc"
  | FunctionApplication { receiver; arguments } ->
      FunctionApplication
        {
          receiver =
            replace_continuations_with_accumulator receiver cloture_rect
              vars_to_replace;
          arguments =
            List.map
              (fun arg ->
                replace_continuations_with_accumulator arg cloture_rect
                  vars_to_replace)
              arguments;
        }
  | PrefixOperation { receiver; operation } ->
      PrefixOperation
        {
          operation;
          receiver =
            replace_continuations_with_accumulator receiver cloture_rect
              vars_to_replace;
        }
  | InfixOperation { lhs; rhs; operation } ->
      InfixOperation
        {
          lhs =
            replace_continuations_with_accumulator lhs cloture_rect
              vars_to_replace;
          rhs =
            replace_continuations_with_accumulator rhs cloture_rect
              vars_to_replace;
          operation;
        }
  | Negation e ->
      Negation
        (replace_continuations_with_accumulator e cloture_rect vars_to_replace)
  | Tuple t ->
      Tuple
        (List.map
           (fun l ->
             replace_continuations_with_accumulator l cloture_rect
               vars_to_replace)
           t)
  | FieldAssignment { receiver; target; value } ->
      FieldAssignment
        {
          receiver =
            replace_continuations_with_accumulator receiver cloture_rect
              vars_to_replace;
          target;
          value =
            replace_continuations_with_accumulator value cloture_rect
              vars_to_replace;
        }
  | ArrayAssignment { receiver; target; value } ->
      ArrayAssignment
        {
          receiver =
            replace_continuations_with_accumulator receiver cloture_rect
              vars_to_replace;
          target =
            replace_continuations_with_accumulator target cloture_rect
              vars_to_replace;
          value =
            replace_continuations_with_accumulator value cloture_rect
              vars_to_replace;
        }
  | ReferenceAssignment { receiver; value } ->
      ReferenceAssignment
        {
          receiver =
            replace_continuations_with_accumulator receiver cloture_rect
              vars_to_replace;
          value =
            replace_continuations_with_accumulator value cloture_rect
              vars_to_replace;
        }
  | If { condition; body; else_body } ->
      If
        {
          condition =
            replace_continuations_with_accumulator condition cloture_rect
              vars_to_replace;
          body =
            replace_continuations_with_accumulator body cloture_rect
              vars_to_replace;
          else_body =
            Option.map
              (fun b ->
                replace_continuations_with_accumulator b cloture_rect
                  vars_to_replace)
              else_body;
        }
  | Sequence s ->
      Sequence
        (List.map
           (fun e ->
             replace_continuations_with_accumulator e cloture_rect
               vars_to_replace)
           s)
  | Match { value; cases } ->
      Match
        {
          value =
            replace_continuations_with_accumulator value cloture_rect
              vars_to_replace;
          cases =
            List.map
              (fun (patterns, e) ->
                ( patterns,
                  replace_continuations_with_accumulator e cloture_rect
                    vars_to_replace ))
              cases;
        }
  | Try { value; cases } ->
      Try
        {
          value =
            replace_continuations_with_accumulator value cloture_rect
              vars_to_replace;
          cases =
            List.map
              (fun (patterns, e) ->
                ( patterns,
                  replace_continuations_with_accumulator e cloture_rect
                    vars_to_replace ))
              cases;
        }
  | FunctionLiteral { style; cases } ->
      FunctionLiteral
        {
          style;
          cases =
            List.map
              (fun (patterns, e) ->
                ( patterns,
                  replace_continuations_with_accumulator e cloture_rect
                    vars_to_replace ))
              cases;
        }
  | LetBinding { bindings; is_rec; inner } ->
      LetBinding
        {
          bindings =
            List.map
              (fun (binding : linear_binding) ->
                match binding with
                | Variable { lhs; value } ->
                    (Variable
                       {
                         lhs;
                         value =
                           replace_continuations_with_accumulator value
                             cloture_rect vars_to_replace;
                       }
                      : linear_binding)
                | Function { name; parameters; body } ->
                    Function
                      {
                        name;
                        parameters;
                        body =
                          replace_continuations_with_accumulator body
                            cloture_rect vars_to_replace;
                      })
              bindings;
          is_rec;
          inner =
            replace_continuations_with_accumulator inner cloture_rect
              vars_to_replace;
        }
  | StringAccess { receiver; target } ->
      StringAccess
        {
          receiver =
            replace_continuations_with_accumulator receiver cloture_rect
              vars_to_replace;
          target =
            replace_continuations_with_accumulator target cloture_rect
              vars_to_replace;
        }
  | StringAssignment { receiver; target; value } ->
      StringAssignment
        {
          receiver =
            replace_continuations_with_accumulator receiver cloture_rect
              vars_to_replace;
          target =
            replace_continuations_with_accumulator target cloture_rect
              vars_to_replace;
          value =
            replace_continuations_with_accumulator value cloture_rect
              vars_to_replace;
        }

(** Given a linear form l that is terminally recursive for a rectifying set
    cloture_rect, replace CPS with the use of an accumulator. The continuations
    are assumed to commute.

    Also removes the elements corresponding to the names in vars_to_remove. This
    allows the variables defining the initial values passed to the continuations
    to be removed. *)
and replace_continuations_with_accumulator (l : linear_form)
    (cloture_rect : variable list) (vars_to_remove : variable list) =
  let rec replace_last_parameter (l : pattern list) =
    match l with
    | [] -> []
    | [ x ] -> [ Ident "acc" ]
    | x :: q -> x :: replace_last_parameter q
  in

  l
  |> List.filter_map (fun (name, elt) ->
         if List.mem name vars_to_remove then None
         else
           Some
             (if elt = Variable "cont" then (name, Variable "acc")
              else if name = "new_cont" then
                match elt with
                | FunctionLiteral f ->
                    ( "new_acc",
                      (* extract_continuation works since we don't call this function unless it worked for all continuations *)
                      FunctionLiteral
                        (extract_continuation_composition f |> Option.get) )
                | _ -> failwith "Not a new continuation"
              else if name = "cont" then
                ( "acc",
                  FunctionApplication
                    {
                      receiver = [ ("new_acc_ref", Variable "new_acc") ];
                      arguments = [ [ ("acc_ref", Variable "acc") ] ];
                    } )
              else
                let new_elt =
                  replace_element_continuations_with_accumulator elt
                    cloture_rect vars_to_remove
                in
                if List.mem name cloture_rect then
                  let new_new_elt =
                    match new_elt with
                    | Variable v -> new_elt
                    | FunctionLiteral { style; cases } ->
                        FunctionLiteral
                          {
                            style;
                            cases =
                              List.map
                                (fun (arguments, body) ->
                                  (replace_last_parameter arguments, body))
                                cases;
                          }
                    | _ -> failwith ("Unable to update definition of " ^ name)
                  in
                  (name, new_new_elt)
                else (name, new_elt)))
