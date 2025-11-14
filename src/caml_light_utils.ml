open Caml_light

type iteration_direction = Inwards | Outwards

let rec map_expression (f : expression -> expression) (e : expression)
    ~(direction : iteration_direction) : expression =
  let e' = if direction = Inwards then f e else e in

  let map_binding (b : binding) : binding =
    match b with
    | Variable { lhs; value } ->
        Variable { lhs; value = map_expression f value ~direction }
    | Function { name; parameters; body } ->
        Function { name; parameters; body = map_expression f body ~direction }
  in

  let e'' =
    match e' with
    | Variable _ -> e'
    | Constant _ -> e'
    | Parenthesised { inner; style } ->
        Parenthesised { style; inner = map_expression f inner ~direction }
    | TypeCoercion { inner; typ } ->
        TypeCoercion { inner = map_expression f inner ~direction; typ }
    | ListLiteral l -> ListLiteral (List.map (map_expression f ~direction) l)
    | ArrayLiteral l -> ArrayLiteral (List.map (map_expression f ~direction) l)
    | RecordLiteral r ->
        RecordLiteral
          (List.map (fun (n, e) -> (n, map_expression f e ~direction)) r)
    | WhileLoop { condition; body } ->
        WhileLoop
          {
            condition = map_expression f condition ~direction;
            body = map_expression f body ~direction;
          }
    | ForLoop { direction = direction'; variable; start; finish; body } ->
        ForLoop
          {
            direction = direction';
            variable;
            start = map_expression f start ~direction;
            finish = map_expression f finish ~direction;
            body = map_expression f body ~direction;
          }
    | Dereference e -> Dereference (map_expression f e ~direction)
    | FieldAccess { receiver; target } ->
        FieldAccess { receiver = map_expression f receiver ~direction; target }
    | ArrayAccess { receiver; target } ->
        ArrayAccess
          {
            receiver = map_expression f receiver ~direction;
            target = map_expression f target ~direction;
          }
    | FunctionApplication { receiver; arguments } ->
        FunctionApplication
          {
            receiver = map_expression f receiver ~direction;
            arguments = List.map (map_expression f ~direction) arguments;
          }
    | PrefixOperation { receiver; operation } ->
        PrefixOperation
          { operation; receiver = map_expression f receiver ~direction }
    | InfixOperation { lhs; rhs; operation } ->
        InfixOperation
          {
            lhs = map_expression f lhs ~direction;
            rhs = map_expression f rhs ~direction;
            operation;
          }
    | Negation e -> Negation (map_expression f e ~direction)
    | Tuple t -> Tuple (List.map (map_expression f ~direction) t)
    | FieldAssignment { receiver; target; value } ->
        FieldAssignment
          {
            receiver = map_expression f receiver ~direction;
            target;
            value = map_expression f value ~direction;
          }
    | ArrayAssignment { receiver; target; value } ->
        ArrayAssignment
          {
            receiver = map_expression f receiver ~direction;
            target = map_expression f target ~direction;
            value = map_expression f value ~direction;
          }
    | ReferenceAssignment { receiver; value } ->
        ReferenceAssignment
          {
            receiver = map_expression f receiver ~direction;
            value = map_expression f value ~direction;
          }
    | If { condition; body; else_body } ->
        If
          {
            condition = map_expression f condition ~direction;
            body = map_expression f body ~direction;
            else_body = Option.map (map_expression f ~direction) else_body;
          }
    | Sequence s -> Sequence (List.map (map_expression f ~direction) s)
    | Match { value; cases } ->
        Match
          {
            value = map_expression f value ~direction;
            cases =
              List.map
                (fun (patterns, e) -> (patterns, map_expression f e ~direction))
                cases;
          }
    | Try { value; cases } ->
        Try
          {
            value = map_expression f value ~direction;
            cases =
              List.map
                (fun (patterns, e) -> (patterns, map_expression f e ~direction))
                cases;
          }
    | FunctionLiteral { style; cases } ->
        FunctionLiteral
          {
            style;
            cases =
              List.map
                (fun (patterns, e) -> (patterns, map_expression f e ~direction))
                cases;
          }
    | LetBinding { bindings; is_rec; inner } ->
        LetBinding
          {
            bindings = List.map map_binding bindings;
            is_rec;
            inner = map_expression ~direction f inner;
          }
    | StringAccess { receiver; target } ->
        StringAccess
          {
            receiver = map_expression ~direction f receiver;
            target = map_expression ~direction f target;
          }
    | StringAssignment { receiver; target; value } ->
        StringAssignment
          {
            receiver = map_expression ~direction f receiver;
            target = map_expression ~direction f target;
            value = map_expression ~direction f value;
          }
  in
  if direction = Outwards then f e'' else e''
