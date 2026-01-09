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
  | FunctionLiteral of {
      style : function_literal_style;
      cases : linear_pattern_cases;
    }
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

and linear_function_ = {
  name : variable node;
  parameters : pattern node list;
  body : linear_form;
}

and linear_binding =
  | Variable of { lhs : pattern node; value : linear_form }
  | Function of linear_function_

and linear_form = (pattern * linear_element) list

let rec last_var (l : linear_form) : variable =
  match l with
  | [] -> failwith "l was empty"
  | (p, _) :: [] -> (
      match p with
      | Ident v -> v
      | _ -> failwith "l did not end with a variable pattern")
  | x :: q -> last_var q

let rec linearize (e : expression) (k : int) : linear_form * int =
  let p (i : int) : pattern = Ident ("a_" ^ string_of_int i) in

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
      (condition_lin @ [ (p k, e_elt) ], k + 2)
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

let rec delinearize_element (e : linear_element) : expression =
  match e with
  | Variable v -> Variable v
  | Constant c -> Constant c
  | Parenthesised { style; inner } ->
      Parenthesised { style; inner = delinearize inner }
  | TypeCoercion { typ; inner } ->
      TypeCoercion { typ; inner = delinearize inner }
  | ListLiteral l -> ListLiteral (List.map delinearize l)
  | ArrayLiteral l -> ArrayLiteral (List.map delinearize l)
  | RecordLiteral l ->
      RecordLiteral
        (List.map (fun (field, value) -> (field, delinearize value)) l)
  | WhileLoop _ -> failwith "Found linearized while loop"
  | ForLoop _ -> failwith "Found linearized for loop"
  | Dereference inner -> Dereference (delinearize inner)
  | FieldAccess { receiver; target } ->
      FieldAccess { receiver = delinearize receiver; target }
  | ArrayAccess { receiver; target } ->
      ArrayAccess
        { receiver = delinearize receiver; target = delinearize target }
  | FunctionApplication { receiver; arguments } ->
      FunctionApplication
        {
          receiver = delinearize receiver;
          arguments = List.map delinearize arguments;
        }
  | PrefixOperation { operation; receiver } ->
      PrefixOperation { operation; receiver = delinearize receiver }
  | InfixOperation { lhs; operation; rhs } ->
      InfixOperation { lhs = delinearize lhs; operation; rhs = delinearize rhs }
  | Negation inner -> Negation (delinearize inner)
  | Tuple l -> Tuple (List.map delinearize l)
  | FieldAssignment { receiver; target; value } ->
      FieldAssignment
        { receiver = delinearize receiver; target; value = delinearize value }
  | ArrayAssignment { receiver; target; value } ->
      ArrayAssignment
        {
          receiver = delinearize receiver;
          target = delinearize target;
          value = delinearize value;
        }
  | ReferenceAssignment { receiver; value } ->
      ReferenceAssignment
        { receiver = delinearize receiver; value = delinearize value }
  | If { condition; body; else_body } ->
      If
        {
          condition = delinearize condition;
          body = delinearize body;
          else_body =
            (match else_body with
            | None -> None
            | Some b -> Some (delinearize b));
        }
  | Sequence s -> Sequence (List.map delinearize s)
  | Match { value; cases } ->
      Match
        {
          value = delinearize value;
          cases =
            List.map (fun (pattern, body) -> (pattern, delinearize body)) cases;
        }
  | Try _ -> failwith "Found linearized try"
  | FunctionLiteral { style; cases } ->
      FunctionLiteral
        {
          style;
          cases =
            List.map (fun (pattern, body) -> (pattern, delinearize body)) cases;
        }
  | LetBinding { bindings; is_rec; inner } ->
      LetBinding
        {
          bindings =
            List.map
              (fun (binding : linear_binding) ->
                match binding with
                | Variable { lhs; value } ->
                    (Variable { lhs; value = delinearize value } : binding)
                | Function _ -> failwith "Found function")
              bindings;
          is_rec;
          inner = delinearize inner;
        }
  | StringAccess { receiver; target } ->
      StringAccess
        { receiver = delinearize receiver; target = delinearize target }
  | StringAssignment { receiver; target; value } ->
      StringAssignment
        {
          receiver = delinearize receiver;
          target = delinearize target;
          value = delinearize value;
        }

and delinearize (l : linear_form) : expression =
  match l with
  | [] -> failwith "Empty linear form"
  | (p, e) :: [] -> delinearize_element e
  | (p, e) :: q ->
      LetBinding
        {
          is_rec = false;
          bindings = [ Variable { lhs = p; value = delinearize_element e } ];
          inner = delinearize q;
        }

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
  (* TODO: Formalise "contains" better to explain this *)
  | FunctionLiteral _ -> false
  | LetBinding { bindings; inner } ->
      contains_application f inner
      || bindings
         |> List.exists (fun (binding : linear_binding) ->
                match binding with
                | Variable { value } -> contains_application f value
                (* TODO: Formalise "contains" better to explain this *)
                | Function _ -> false)
  | StringAccess { receiver; target } ->
      contains_application f receiver || contains_application f target
  | StringAssignment { receiver; target; value } ->
      contains_application f receiver
      || contains_application f target
      || contains_application f value

and contains_application (f : variable) (l : linear_form) : bool =
  match l with
  | [] -> false
  | (p, e) :: q -> element_contains_application f e || contains_application f q

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
  | FunctionLiteral { style; cases } ->
      FunctionLiteral
        {
          style;
          cases = List.map (fun (pattern, body) -> (pattern, f body)) cases;
        }
  (* No locally terminal children *)
  | _ -> e

let rec rectify (l : linear_form) (e_rect : variable list) (cont : variable)
    (new_name : variable -> variable) : linear_form =
  let rec find_first_recursive_element (tail : linear_form) (head : linear_form)
      : linear_form * ((pattern * linear_element) * linear_form) option =
    match tail with
    | [] -> (List.rev head, None)
    | (p, e) :: q ->
        if List.exists (fun f -> element_contains_application f e) e_rect then
          (List.rev head, Some ((p, e), q))
        else find_first_recursive_element q ((p, e) :: head)
  in
  let l_1, maybe_recursive = find_first_recursive_element l [] in
  match maybe_recursive with
  | None ->
      let head_var = last_var l_1 in
      l_1
      @ [
          ( Ident "cont_res",
            FunctionApplication
              {
                receiver = [ (Ident "cont_call", Variable cont) ];
                arguments = [ [ (Ident "cont_arg", Variable head_var) ] ];
              } );
        ]
  | Some ((a, e), l_2) -> (
      match l_2 with
      | [] ->
          let e_rec =
            match e with
            | FunctionApplication { receiver = [ (p, Variable f) ]; arguments }
              when List.mem f e_rect ->
                FunctionApplication
                  {
                    receiver = [ (p, Variable (new_name f)) ];
                    arguments =
                      arguments @ [ [ (Ident "cont_arg", Variable cont) ] ];
                  }
            | _ ->
                map_locally_terminal_children
                  (fun f -> rectify f e_rect cont new_name)
                  e
          in
          l_1 @ [ (a, e_rec) ]
      | _ ->
          let l_2_rec = rectify l_2 e_rect cont new_name in
          let cont' = cont ^ "'" in
          let e_rec =
            match e with
            | FunctionApplication { receiver = [ (p, Variable f) ]; arguments }
              when List.mem f e_rect ->
                FunctionApplication
                  {
                    receiver = [ (p, Variable (new_name f)) ];
                    arguments =
                      arguments @ [ [ (Ident "cont_arg", Variable cont') ] ];
                  }
            | _ ->
                map_locally_terminal_children
                  (fun f -> rectify f e_rect cont' new_name)
                  e
          in
          l_1
          @ [
              ( Ident cont',
                FunctionLiteral { style = Fun; cases = [ ([ a ], l_2_rec) ] } );
              (a, e_rec);
            ])
