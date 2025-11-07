open Caml_light

let source =
  let source_f = open_in "../test.ml" in
  let source = really_input_string source_f (in_channel_length source_f) in
  close_in source_f;
  source

let ast = parse_caml_light_ast source

let next_ident (t : (string, string) Hashtbl.t) (prefix : string) =
  prefix ^ "_" ^ string_of_int (Hashtbl.length t)

(* Obfuscates the program *)
let transform (ast : program) : program =
  let global_value_scope = Hashtbl.create 8 in
  let global_type_scope = Hashtbl.create 8 in
  let global_constructor_scope = Hashtbl.create 8 in

  let subst (scope : (string, string) Hashtbl.t) ?(prefix : string option)
      (s : string) : string =
    match Hashtbl.find_opt scope s with
    | Some s' -> s'
    | None -> (
        match prefix with
        | Some prefix ->
            let res = next_ident scope prefix in
            Hashtbl.add scope s res;
            res
        | None -> s)
  in

  let rec transform_type_expression (e : type_expression) =
    match e with
    | Argument n -> Argument (subst ~prefix:"a" global_type_scope n)
    | Parenthesised e -> Parenthesised (transform_type_expression e)
    | Construction c ->
        Construction
          {
            constructor = subst global_type_scope c.constructor;
            arguments = List.map transform_type_expression c.arguments;
          }
    | Tuple t -> Tuple (List.map transform_type_expression t)
    | Function f ->
        Function
          {
            argument = transform_type_expression f.argument;
            result = transform_type_expression f.result;
          }
  in

  let transform_constructor (c : constructor) =
    match c with Named n -> Named (subst global_constructor_scope n) | _ -> c
  in

  let transform_constant (c : constant) =
    match c with
    | Construction c -> Construction (transform_constructor c)
    | _ -> c
  in

  let rec transform_pattern (p : pattern) =
    match p with
    | Ident e -> Ident (subst ~prefix:"x" global_value_scope e)
    | Underscore -> Underscore
    | Parenthesised p -> Parenthesised (transform_pattern p)
    | TypeCoercion c ->
        TypeCoercion
          {
            inner = transform_pattern c.inner;
            typ = transform_type_expression c.typ;
          }
    | Constant c -> Constant (transform_constant c)
    | Record r ->
        Record
          (List.map
             (fun (label, pattern) ->
               (subst global_value_scope label, transform_pattern pattern))
             r)
    | List l -> List (List.map transform_pattern l)
    | Construction c ->
        Construction
          {
            constructor = transform_constructor c.constructor;
            argument = transform_pattern c.argument;
          }
    | Concatenation c ->
        Concatenation
          { head = transform_pattern c.head; tail = transform_pattern c.tail }
    | Tuple t -> Tuple (List.map transform_pattern t)
    | Or o -> Or (List.map transform_pattern o)
    | As a ->
        As
          {
            inner = transform_pattern a.inner;
            name = subst ~prefix:"x" global_value_scope a.name;
          }
  in

  let rec transform_binding (b : binding) : binding =
    match b with
    | Variable v ->
        let lhs = transform_pattern v.lhs in
        Variable { lhs; value = transform_expression v.value }
    | Function f ->
        let name = subst ~prefix:"mystere" global_value_scope f.name in
        let parameters = List.map transform_pattern f.parameters in
        Function { name; parameters; value = transform_expression f.value }
  and transform_expression (e : expression) : expression =
    match e with
    | Variable v -> Variable (subst global_value_scope v)
    | Constant c -> Constant (transform_constant c)
    | Parenthesised e ->
        Parenthesised { inner = transform_expression e.inner; style = e.style }
    | TypeCoercion e ->
        TypeCoercion
          {
            inner = transform_expression e.inner;
            typ = transform_type_expression e.typ;
          }
    | ListLiteral l -> ListLiteral (List.map transform_expression l)
    | ArrayLiteral l -> ArrayLiteral (List.map transform_expression l)
    | RecordLiteral l ->
        RecordLiteral
          (List.map
             (fun (label, expr) ->
               (subst global_value_scope label, transform_expression expr))
             l)
    | WhileLoop l ->
        WhileLoop
          {
            condition = transform_expression l.condition;
            body = transform_expression l.body;
          }
    | ForLoop l ->
        let variable = subst ~prefix:"x" global_value_scope l.variable in
        ForLoop
          {
            direction = l.direction;
            variable;
            start = transform_expression l.start;
            finish = transform_expression l.finish;
            body = transform_expression l.body;
          }
    | Dereference e -> Dereference (transform_expression e)
    | FieldAccess a ->
        FieldAccess
          {
            receiver = transform_expression a.receiver;
            target = subst global_value_scope a.target;
          }
    | ArrayAccess a ->
        ArrayAccess
          {
            receiver = transform_expression a.receiver;
            target = transform_expression a.target;
          }
    | FunctionApplication f ->
        FunctionApplication
          {
            receiver = transform_expression f.receiver;
            arguments = List.map transform_expression f.arguments;
          }
    | PrefixOperation o ->
        PrefixOperation
          {
            operation = o.operation;
            receiver = transform_expression o.receiver;
          }
    | InfixOperation o ->
        InfixOperation
          {
            lhs = transform_expression o.lhs;
            operation = o.operation;
            rhs = transform_expression o.rhs;
          }
    | Negation n -> Negation (transform_expression n)
    | Tuple t -> Tuple (List.map transform_expression t)
    | FieldAssignment a ->
        FieldAssignment
          {
            receiver = transform_expression a.receiver;
            target = subst global_value_scope a.target;
            value = transform_expression a.value;
          }
    | ArrayAssignment a ->
        ArrayAssignment
          {
            receiver = transform_expression a.receiver;
            target = transform_expression a.target;
            value = transform_expression a.value;
          }
    | ReferenceAssignment a ->
        ReferenceAssignment
          {
            receiver = transform_expression a.receiver;
            value = transform_expression a.value;
          }
    | If i ->
        If
          {
            condition = transform_expression i.condition;
            body = transform_expression i.body;
            else_body =
              (match i.else_body with
              | None -> None
              | Some b -> Some (transform_expression b));
          }
    | Sequence s -> Sequence (List.map transform_expression s)
    | Match m ->
        Match
          {
            value = transform_expression m.value;
            cases =
              List.map
                (fun (patterns, expr) ->
                  let patterns = List.map transform_pattern patterns in
                  (patterns, transform_expression expr))
                m.cases;
          }
    | Try t ->
        Try
          {
            value = transform_expression t.value;
            cases =
              List.map
                (fun (patterns, expr) ->
                  let patterns = List.map transform_pattern patterns in
                  (patterns, transform_expression expr))
                t.cases;
          }
    | FunctionLiteral f ->
        FunctionLiteral
          {
            style = f.style;
            cases =
              List.map
                (fun (patterns, expr) ->
                  let patterns = List.map transform_pattern patterns in
                  (patterns, transform_expression expr))
                f.cases;
          }
    | LetBinding l ->
        let bindings = List.map transform_binding l.bindings in
        LetBinding
          { bindings; is_rec = l.is_rec; inner = transform_expression l.inner }
    | StringAccess s ->
        StringAccess
          {
            receiver = transform_expression s.receiver;
            target = transform_expression s.target;
          }
    | StringAssignment a ->
        StringAssignment
          {
            receiver = transform_expression a.receiver;
            target = transform_expression a.target;
            value = transform_expression a.value;
          }
  in

  let transform_value_definition (v : value_definition) =
    { is_rec = v.is_rec; bindings = List.map transform_binding v.bindings }
  in

  let transform_constructor_declaration (c : type_constructor_declaration) =
    {
      name = subst ~prefix:"C" global_constructor_scope c.name;
      parameter =
        (match c.parameter with
        | None -> None
        | Some p -> Some (transform_type_expression p));
    }
  in

  let transform_field_declaration (f : field_declaration) =
    {
      name = subst ~prefix:"x" global_value_scope f.name;
      is_mutable = f.is_mutable;
      typ = transform_type_expression f.typ;
    }
  in

  let transform_typedef (t : typedef) =
    match t with
    | Constructors c ->
        let name = subst ~prefix:"typ" global_type_scope c.name in
        let parameters =
          List.map (subst ~prefix:"a" global_type_scope) c.parameters
        in
        Constructors
          {
            name;
            parenthesised_parameters = c.parenthesised_parameters;
            parameters;
            constructors =
              List.map transform_constructor_declaration c.constructors;
          }
    | Record r ->
        let name = subst ~prefix:"typ" global_type_scope r.name in
        let parameters =
          List.map (subst ~prefix:"a" global_type_scope) r.parameters
        in
        Record
          {
            name;
            parenthesised_parameters = r.parenthesised_parameters;
            parameters;
            fields = List.map transform_field_declaration r.fields;
          }
    | Alias a ->
        let name = subst ~prefix:"typ" global_type_scope a.name in
        let parameters =
          List.map (subst ~prefix:"a" global_type_scope) a.parameters
        in
        Alias
          {
            name;
            style = a.style;
            parenthesised_parameters = a.parenthesised_parameters;
            parameters;
            aliased = transform_type_expression a.aliased;
          }
    | Anonymous a ->
        let name = subst ~prefix:"typ" global_type_scope a.name in
        let parameters =
          List.map (subst ~prefix:"a" global_type_scope) a.parameters
        in
        Anonymous
          {
            name;
            parenthesised_parameters = a.parenthesised_parameters;
            parameters;
          }
  in

  let transform_type_definition (t : type_definition) =
    List.map transform_typedef t
  in

  let transform_exception_definition (e : exception_definition) =
    { exceptions = List.map transform_constructor_declaration e.exceptions }
  in

  let transform_phrase (phrase : phrase) : phrase =
    match phrase with
    | Expression e -> Expression (transform_expression e)
    | ValueDefinition v -> ValueDefinition (transform_value_definition v)
    | TypeDefinition t -> TypeDefinition (transform_type_definition t)
    | ExceptionDefinition e ->
        ExceptionDefinition (transform_exception_definition e)
  in

  List.map transform_phrase ast

let transformed_ast = transform ast;;

print_endline (string_of_ast transformed_ast)
