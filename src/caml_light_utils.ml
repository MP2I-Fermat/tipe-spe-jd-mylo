open Caml_light

let rec map_expression (f : expression -> expression) (e : expression) :
    expression =
  let e' = f e in

  let map_binding (b : binding) : binding =
    match b with
    | Variable { lhs; value } ->
        Variable { lhs; value = map_expression f value }
    | Function { name; parameters; body } ->
        Function { name; parameters; body = map_expression f body }
  in

  let e'' =
    match e' with
    | Variable _ -> e'
    | Constant _ -> e'
    | Parenthesised { inner; style } ->
        Parenthesised { style; inner = map_expression f inner }
    | TypeCoercion { inner; typ } ->
        TypeCoercion { inner = map_expression f inner; typ }
    | ListLiteral l -> ListLiteral (List.map (map_expression f) l)
    | ArrayLiteral l -> ArrayLiteral (List.map (map_expression f) l)
    | RecordLiteral r ->
        RecordLiteral (List.map (fun (n, e) -> (n, map_expression f e)) r)
    | WhileLoop { condition; body } ->
        WhileLoop
          {
            condition = map_expression f condition;
            body = map_expression f body;
          }
    | ForLoop { direction; variable; start; finish; body } ->
        ForLoop
          {
            direction;
            variable;
            start = map_expression f start;
            finish = map_expression f finish;
            body = map_expression f body;
          }
    | Dereference e -> Dereference (map_expression f e)
    | FieldAccess { receiver; target } ->
        FieldAccess { receiver = map_expression f receiver; target }
    | ArrayAccess { receiver; target } ->
        ArrayAccess
          {
            receiver = map_expression f receiver;
            target = map_expression f target;
          }
    | FunctionApplication { receiver; arguments } ->
        FunctionApplication
          {
            receiver = map_expression f receiver;
            arguments = List.map (map_expression f) arguments;
          }
    | PrefixOperation { receiver; operation } ->
        PrefixOperation { operation; receiver = map_expression f receiver }
    | InfixOperation { lhs; rhs; operation } ->
        InfixOperation
          { lhs = map_expression f lhs; rhs = map_expression f rhs; operation }
    | Negation e -> Negation (map_expression f e)
    | Tuple t -> Tuple (List.map (map_expression f) t)
    | FieldAssignment { receiver; target; value } ->
        FieldAssignment
          {
            receiver = map_expression f receiver;
            target;
            value = map_expression f value;
          }
    | ArrayAssignment { receiver; target; value } ->
        ArrayAssignment
          {
            receiver = map_expression f receiver;
            target = map_expression f target;
            value = map_expression f value;
          }
    | ReferenceAssignment { receiver; value } ->
        ReferenceAssignment
          {
            receiver = map_expression f receiver;
            value = map_expression f value;
          }
    | If { condition; body; else_body } ->
        If
          {
            condition = map_expression f condition;
            body = map_expression f body;
            else_body = Option.map (map_expression f) else_body;
          }
    | Sequence s -> Sequence (List.map (map_expression f) s)
    | Match { value; cases } ->
        Match
          {
            value = map_expression f value;
            cases =
              List.map
                (fun (patterns, e) -> (patterns, map_expression f e))
                cases;
          }
    | Try { value; cases } ->
        Try
          {
            value = map_expression f value;
            cases =
              List.map
                (fun (patterns, e) -> (patterns, map_expression f e))
                cases;
          }
    | FunctionLiteral { style; cases } ->
        FunctionLiteral
          {
            style;
            cases =
              List.map
                (fun (patterns, e) -> (patterns, map_expression f e))
                cases;
          }
    | LetBinding { bindings; is_rec; inner } ->
        LetBinding
          {
            bindings = List.map map_binding bindings;
            is_rec;
            inner = map_expression f inner;
          }
    | StringAccess { receiver; target } ->
        StringAccess
          {
            receiver = map_expression f receiver;
            target = map_expression f target;
          }
    | StringAssignment { receiver; target; value } ->
        StringAssignment
          {
            receiver = map_expression f receiver;
            target = map_expression f target;
            value = map_expression f value;
          }
  in
  f e''
