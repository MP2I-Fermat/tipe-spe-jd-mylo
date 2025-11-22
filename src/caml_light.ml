open Utils
open Lexer
open Regex_grammar
open Parser
open Grammar_grammar

(** The token rules and grammar rules for parsing Caml Light. *)
let caml_light_tokens, caml_light_grammar =
  let caml_light_grammar_definition_fp = open_in "../caml_light.grammar" in
  let caml_light_grammar_definition =
    really_input_string caml_light_grammar_definition_fp
      (in_channel_length caml_light_grammar_definition_fp)
  in
  close_in caml_light_grammar_definition_fp;
  parse_grammar caml_light_grammar_definition

(** The LR(1) automaton built from the Caml Light grammar. *)
let caml_light_automaton =
  construit_automate_LR1 caml_light_grammar "IMPLEMENTATION" "<eof>"

(** Collapses precedence rules for target in tree.

    Parsing ambiguities in grammars are resolved by introducing precedence
    levels that indicate which groupings should be preferred.

    However, such a solution leads to the syntax tree containing many variants
    of what is semantically only one rule.

    This method collapses all occurrences of variants of a rule into a single
    node type.

    The resulting node type is defined by target. A node is considered to be a
    variant of target if its node type is prefixed by target, *)
let rec collapse_precedence (target : string)
    (tree : (string, string) syntax_tree) : (string, string) syntax_tree =
  match tree with
  | Node (nt1, [ Node (nt2, children) ])
    when nt1 = target && String.starts_with ~prefix:target nt2 ->
      collapse_precedence target (Node (target, children))
  | Node (nt, children)
    when nt <> target && String.starts_with ~prefix:target nt ->
      collapse_precedence target (Node (target, children))
  | Node (nt, children) ->
      Node (nt, List.map (collapse_precedence target) children)
  | _ -> tree

(** Parses Caml Light source into a syntax tree. *)
let parse_caml_light_syntax_tree (source : string) =
  (* Additional token rules for separating syntax elements (whitespace) and
     parsing comments (comment_start, comment_end, unrecognizable - which
     is allowed within a comment).  *)
  let enhanced_token_rules =
    List.rev_append caml_light_tokens
      [
        (parse_regex "( |\\n|\\t)+", "<whitespace>");
        (parse_regex "\\(\\*", "<comment_start>");
        (parse_regex "\\*\\)", "<comment_end>");
      ]
  in
  let tokens =
    tokenize enhanced_token_rules "<eof>" "<unrecognizable>" source
  in

  let rec filter_tokens_from (tokens : string token list) (comment_level : int)
      (res : string token list) =
    if comment_level < 0 then failwith "Too many comment end tags"
    else
      match tokens with
      | [] -> List.rev res
      | x :: q -> (
          match x.token_type with
          | "<comment_start>" -> filter_tokens_from q (comment_level + 1) res
          | "<comment_end>" -> filter_tokens_from q (comment_level - 1) res
          | "<whitespace>" -> filter_tokens_from q comment_level res
          | _ ->
              if comment_level > 0 then filter_tokens_from q comment_level res
              else filter_tokens_from q comment_level (x :: res))
  in

  let filtered_tokens = filter_tokens_from tokens 0 [] in
  parse caml_light_automaton "<eof>" filtered_tokens "IMPLEMENTATION"
  |> collapse_precedence "EXPR"
  |> collapse_precedence "PATTERN"
  |> collapse_precedence "TYP_EXPR"
  |> collapse_precedence "IMPL_PHRASE"
  |> collapse_precedence "IMPLEMENTATION"

type 'a node = 'a
and program = phrase node list node

and phrase =
  | Expression of expression node
  | ValueDefinition of value_definition node
  | TypeDefinition of type_definition node
  | ExceptionDefinition of exception_definition node

and parenthesis_style = Parenthesis | BeginEnd
and for_direction = Up | Down
and prefix_operation = Minus | MinusDot

and infix_operation =
  | DoubleStar
  | Mod
  | Star
  | StarDot
  | Slash
  | SlashDot
  | Plus
  | PlusDot
  | Minus
  | MinusDot
  | DoubleColon
  | At
  | Caret
  | Eq
  | Neq
  | DoubleEq
  | BangEq
  | Less
  | Leq
  | Greater
  | Geq
  | LessDot
  | LeqDot
  | GreaterDot
  | GeqDot
  | Ampersand
  | Or
  | DoubleAmpersand
  | DoublePipe

and pattern_cases = (pattern node list * expression node) list
and function_literal_style = Fun | Function
and label = string
and lowercase_ident = string
and uppercase_ident = string
and variable = string
and type_constructor = string

and constructor =
  | Named of uppercase_ident node
  | EmptyList
  | Unit of parenthesis_style
  | EmptyArray

and function_ = {
  name : variable node;
  parameters : pattern node list;
  body : expression node;
}

and binding =
  | Variable of { lhs : pattern node; value : expression node }
  | Function of function_

and expression =
  | Variable of variable node
  | Constant of constant node
  | Parenthesised of { inner : expression node; style : parenthesis_style }
  | TypeCoercion of { inner : expression node; typ : type_expression node }
  | ListLiteral of expression node list
  | ArrayLiteral of expression node list
  | RecordLiteral of (label node * expression node) list
  | WhileLoop of { condition : expression node; body : expression node }
  | ForLoop of {
      direction : for_direction;
      variable : lowercase_ident node;
      start : expression node;
      finish : expression node;
      body : expression node;
    }
  | Dereference of expression node
  | FieldAccess of { receiver : expression node; target : label node }
  | ArrayAccess of { receiver : expression node; target : expression node }
  | FunctionApplication of {
      receiver : expression node;
      arguments : expression node list;
    }
  | PrefixOperation of {
      receiver : expression node;
      operation : prefix_operation;
    }
  | InfixOperation of {
      lhs : expression node;
      rhs : expression node;
      operation : infix_operation;
    }
  | Negation of expression node
  | Tuple of expression node list
  | FieldAssignment of {
      receiver : expression node;
      target : label node;
      value : expression node;
    }
  | ArrayAssignment of {
      receiver : expression node;
      target : expression node;
      value : expression node;
    }
  | ReferenceAssignment of {
      receiver : expression node;
      value : expression node;
    }
  | If of {
      condition : expression node;
      body : expression node;
      else_body : expression node option;
    }
  | Sequence of expression node list
  | Match of { value : expression node; cases : pattern_cases }
  | Try of { value : expression node; cases : pattern_cases }
  | FunctionLiteral of { style : function_literal_style; cases : pattern_cases }
  | LetBinding of {
      bindings : binding node list;
      is_rec : bool;
      inner : expression node;
    }
  | StringAccess of { receiver : expression node; target : expression node }
  | StringAssignment of {
      receiver : expression node;
      target : expression node;
      value : expression node;
    }

and pattern =
  | Ident of lowercase_ident node
  | Underscore
  | Parenthesised of pattern node
  | TypeCoercion of { inner : pattern node; typ : type_expression node }
  | Constant of constant node
  | Record of (label node * pattern node) list
  | List of pattern node list
  | Construction of { constructor : constructor node; argument : pattern node }
  | Concatenation of { head : pattern node; tail : pattern node }
  | Tuple of pattern node list
  | Or of pattern node list
  | As of { inner : pattern node; name : lowercase_ident node }

and type_expression =
  | Argument of lowercase_ident node
  | Parenthesised of type_expression node
  | Construction of {
      constructor : type_constructor node;
      arguments : type_expression node list;
    }
  | Tuple of type_expression node list
  | Function of {
      argument : type_expression node;
      result : type_expression node;
    }

and char_literal_style = Old | New

and constant =
  | IntegerLiteral of int
  | FloatLiteral of float
  | CharacterLiteral of { style : char_literal_style; value : char }
  | StringLiteral of string
  | Construction of constructor node

and value_definition = { bindings : binding node list; is_rec : bool }
and type_definition = typedef node list
and type_alias_style = DoubleEq | SingleEq

and field_declaration = {
  name : lowercase_ident node;
  is_mutable : bool;
  typ : type_expression node;
}

and type_constructor_declaration = {
  name : uppercase_ident node;
  parameter : type_expression node option;
}

and typedef =
  | Constructors of {
      name : lowercase_ident node;
      parameters : lowercase_ident node list;
      parenthesised_parameters : bool;
      constructors : type_constructor_declaration node list;
    }
  | Record of {
      name : lowercase_ident node;
      parameters : lowercase_ident node list;
      parenthesised_parameters : bool;
      fields : field_declaration node list;
    }
  | Alias of {
      name : lowercase_ident node;
      style : type_alias_style;
      parameters : lowercase_ident node list;
      parenthesised_parameters : bool;
      aliased : type_expression node;
    }
  | Anonymous of {
      name : lowercase_ident node;
      parameters : lowercase_ident node list;
      parenthesised_parameters : bool;
    }

and exception_definition = {
  exceptions : type_constructor_declaration node list;
}

(** Converts a Caml Light syntax_tree to a Caml Light AST. *)
let rec ast_of_syntax_tree (tree : (string, string) syntax_tree) : program =
  let rec label (tree : (string, string) syntax_tree) : label node =
    match tree with
    | Node ("LABEL", [ Leaf { token_type = "lowercase_ident"; value } ]) ->
        value
    | _ -> failwith "Not a label"
  and variable (tree : (string, string) syntax_tree) : variable node =
    match tree with
    | Node ("VARIABLE", [ Leaf { token_type = "lowercase_ident"; value } ]) ->
        value
    | _ -> failwith "Not a variable"
  and constructor (tree : (string, string) syntax_tree) : constructor node =
    match tree with
    | Node ("CONSTR", [ Leaf { token_type = "uppercase_ident"; value } ]) ->
        Named value
    | Node
        ( "CONSTR",
          [
            Leaf { token_type = "open_bracket" };
            Leaf { token_type = "close_bracket" };
          ] ) ->
        EmptyList
    | Node
        ( "CONSTR",
          [
            Leaf { token_type = "open_paren" };
            Leaf { token_type = "close_paren" };
          ] ) ->
        Unit Parenthesis
    | Node
        ( "CONSTR",
          [
            Leaf { token_type = "open_bracket_bar" };
            Leaf { token_type = "close_bracket_bar" };
          ] ) ->
        EmptyArray
    | Node
        ( "CONSTR",
          [ Leaf { token_type = "begin" }; Leaf { token_type = "end" } ] ) ->
        Unit BeginEnd
    | _ -> failwith "Not a constructor"
  and type_constructor (tree : (string, string) syntax_tree) :
      type_constructor node =
    match tree with
    | Node ("TYPE_CONSTR", [ Leaf { token_type = "lowercase_ident"; value } ])
      ->
        value
    | _ -> failwith "Not a type constructor"
  and more_type_constructor_arguments (tree : (string, string) syntax_tree) :
      type_expression node list =
    match tree with
    | Node ("MORE_TYP_CONSTR_ARGS", [ inner ]) -> [ type_expression inner ]
    | Node
        ("MORE_TYP_CONSTR_ARGS", [ inner; Leaf { token_type = "comma" }; rest ])
      ->
        type_expression inner :: more_type_constructor_arguments rest
    | _ -> failwith "Not a type expression argument list"
  and tuple_type_expression (tree : (string, string) syntax_tree) :
      type_expression node list =
    match tree with
    | Node ("TYP_EXPR", [ first; Leaf { token_type = "star" }; rest ]) ->
        type_expression first :: tuple_type_expression rest
    | _ -> [ type_expression tree ]
  and type_expression (tree : (string, string) syntax_tree) :
      type_expression node =
    match tree with
    | Node
        ( "TYP_EXPR",
          [
            Leaf { token_type = "apostrophe" };
            Leaf { token_type = "lowercase_ident"; value };
          ] ) ->
        Argument value
    | Node
        ( "TYP_EXPR",
          [
            Leaf { token_type = "open_paren" };
            inner;
            Leaf { token_type = "close_paren" };
          ] ) ->
        Parenthesised (type_expression inner)
    | Node ("TYP_EXPR", [ (Node ("TYPE_CONSTR", _) as constructor) ]) ->
        let constructor_node = type_constructor constructor in

        Construction { constructor = constructor_node; arguments = [] }
    | Node
        ( "TYP_EXPR",
          [
            (Node ("TYP_EXPR", _) as argument);
            (Node ("TYPE_CONSTR", _) as constructor);
          ] ) ->
        let constructor_node = type_constructor constructor in
        let argument_node = type_expression argument in

        Construction
          { constructor = constructor_node; arguments = [ argument_node ] }
    | Node
        ( "TYP_EXPR",
          [
            Leaf { token_type = "open_paren" };
            first_argument;
            Leaf { token_type = "comma" };
            more_arguments;
            Leaf { token_type = "close_paren" };
            constructor;
          ] ) ->
        let arguments =
          type_expression first_argument
          :: more_type_constructor_arguments more_arguments
        in
        let constructor_node = type_constructor constructor in
        Construction { constructor = constructor_node; arguments }
    | Node ("TYP_EXPR", [ _; Leaf { token_type = "star" }; _ ]) ->
        let inner_expression_nodes = tuple_type_expression tree in

        Tuple inner_expression_nodes
    | Node
        ("TYP_EXPR", [ argument; Leaf { token_type = "right_arrow" }; result ])
      ->
        let argument_node = type_expression argument in
        let result_node = type_expression result in
        Function { argument = argument_node; result = result_node }
    | _ -> failwith "Not a type expression"
  and constant (tree : (string, string) syntax_tree) : constant node =
    match tree with
    | Node ("CONSTANT", [ Leaf { token_type = "integer_literal"; value } ]) ->
        IntegerLiteral (int_of_string value)
    | Node ("CONSTANT", [ Leaf { token_type = "float_literal"; value } ]) ->
        FloatLiteral (float_of_string value)
    | Node ("CONSTANT", [ Leaf { token_type = "char_literal"; value } ]) ->
        CharacterLiteral { value = value.[1]; style = Old }
    | Node ("CONSTANT", [ Leaf { token_type = "string_literal"; value } ]) ->
        StringLiteral (String.sub value 1 (String.length value - 2))
    | Node ("CONSTANT", [ (Node ("CONSTR", _) as constr) ]) ->
        let constr_node = constructor constr in
        Construction constr_node
    | Node ("CONSTANT", [ Leaf { token_type = "modern_char_literal"; value } ])
      ->
        CharacterLiteral { value = value.[0]; style = New }
    | _ -> failwith "Not a constant"
  and field_pattern (tree : (string, string) syntax_tree) :
      label node * pattern node =
    match tree with
    | Node ("FIELD_PATTERN", [ lbl; Leaf { token_type = "eq" }; pttrn ]) ->
        (label lbl, pattern pttrn)
    | _ -> failwith "Not a field pattern"
  and field_pattern_list (tree : (string, string) syntax_tree) :
      (label node * pattern node) list =
    match tree with
    | Node ("FIELD_PATTERN_LIST", [ inner ]) -> [ field_pattern inner ]
    | Node
        ( "FIELD_PATTERN_LIST",
          [ inner; Leaf { token_type = "semicolon" }; rest ] ) ->
        field_pattern inner :: field_pattern_list rest
    | _ -> failwith "Not a field pattern lit"
  and a_pattern_list (tree : (string, string) syntax_tree) : pattern node list =
    match tree with
    | Node ("A_PATTERN_LIST", [ pttrn ]) -> [ pattern pttrn ]
    | Node ("A_PATTERN_LIST", [ pttrn; Leaf { token_type = "semicolon" }; rest ])
      ->
        pattern pttrn :: a_pattern_list rest
    | _ -> failwith "Not an A pattern list"
  and pattern_tuple (tree : (string, string) syntax_tree) : pattern node list =
    match tree with
    | Node ("PATTERN", [ rest; Leaf { token_type = "comma" }; last ]) ->
        pattern_tuple rest @ [ pattern last ]
    | _ -> [ pattern tree ]
  and pattern_or (tree : (string, string) syntax_tree) : pattern node list =
    match tree with
    | Node ("PATTERN", [ rest; Leaf { token_type = "pipe" }; last ]) ->
        pattern_or rest @ [ pattern last ]
    | _ -> [ pattern tree ]
  and pattern (tree : (string, string) syntax_tree) : pattern node =
    match tree with
    | Node ("PATTERN", [ Leaf { token_type = "lowercase_ident"; value } ]) ->
        Ident value
    | Node ("PATTERN", [ Leaf { token_type = "underscore" } ]) -> Underscore
    | Node
        ( "PATTERN",
          [
            Leaf { token_type = "open_paren" };
            inner;
            Leaf { token_type = "close_paren" };
          ] ) ->
        Parenthesised (pattern inner)
    | Node
        ( "PATTERN",
          [
            Leaf { token_type = "open_paren" };
            inner;
            Leaf { token_type = "colon" };
            typ_expr;
            Leaf { token_type = "close_paren" };
          ] ) ->
        TypeCoercion { inner = pattern inner; typ = type_expression typ_expr }
    | Node ("PATTERN", [ (Node ("CONSTANT", _) as cst) ]) ->
        let cst_node = constant cst in
        Constant cst_node
    | Node
        ( "PATTERN",
          [
            Leaf { token_type = "open_brace" };
            fields;
            Leaf { token_type = "close_brace" };
          ] ) ->
        Record (field_pattern_list fields)
    | Node
        ( "PATTERN",
          [
            Leaf { token_type = "open_bracket" };
            patterns;
            Leaf { token_type = "close_bracket" };
          ] ) ->
        List (a_pattern_list patterns)
    | Node ("PATTERN", [ constr; pttrn ]) ->
        let constr_node = constructor constr in
        let pttrn_node = pattern pttrn in

        Construction { constructor = constr_node; argument = pttrn_node }
    | Node ("PATTERN", [ first; Leaf { token_type = "double_colon" }; rest ]) ->
        let first_node = pattern first in
        let rest_node = pattern rest in
        Concatenation { head = first_node; tail = rest_node }
    | Node ("PATTERN", [ _; Leaf { token_type = "comma" }; _ ]) ->
        let pattern_nodes = pattern_tuple tree in
        Tuple pattern_nodes
    | Node ("PATTERN", [ _; Leaf { token_type = "pipe" }; _ ]) ->
        let pattern_nodes = pattern_or tree in
        Or pattern_nodes
    | Node
        ( "PATTERN",
          [
            inner;
            Leaf { token_type = "as" };
            Leaf { token_type = "lowercase_ident"; value };
          ] ) ->
        let inner_node = pattern inner in
        As { inner = inner_node; name = value }
    | _ -> failwith "Not a pattern"
  and simple_matching (tree : (string, string) syntax_tree) : pattern_cases =
    match tree with
    | Node
        ("SIMPLE_MATCHING", [ pttrn; Leaf { token_type = "right_arrow" }; expr ])
      ->
        let pttrn_node = pattern pttrn in
        let expr_node = expression expr in
        [ ([ pttrn_node ], expr_node) ]
    | Node
        ( "SIMPLE_MATCHING",
          [
            pttrn;
            Leaf { token_type = "right_arrow" };
            expr;
            Leaf { token_type = "pipe" };
            other_cases;
          ] ) ->
        let other_cases_nodes = simple_matching other_cases in
        let pttrn_node = pattern pttrn in
        let expr_node = expression expr in
        ([ pttrn_node ], expr_node) :: other_cases_nodes
    | _ -> failwith "Not a simple matching"
  and b_pattern_list (tree : (string, string) syntax_tree) : pattern node list =
    match tree with
    | Node ("B_PATTERN_LIST", [ inner ]) -> [ pattern inner ]
    | Node ("B_PATTERN_LIST", [ inner; rest ]) ->
        pattern inner :: b_pattern_list rest
    | _ -> failwith "Not a B pattern list"
  and multiple_matching (tree : (string, string) syntax_tree) : pattern_cases =
    match tree with
    | Node
        ( "MULTIPLE_MATCHING",
          [ patterns; Leaf { token_type = "right_arow" }; expr ] ) ->
        let pattern_nodes = b_pattern_list patterns in
        let expr_node = expression expr in
        [ (pattern_nodes, expr_node) ]
    | Node
        ( "MULTIPLE_MATCHING",
          [
            patterns;
            Leaf { token_type = "right_arow" };
            expr;
            Leaf { token_type = "pipe" };
            rest;
          ] ) ->
        let rest_node = multiple_matching rest in
        let pattern_nodes = b_pattern_list patterns in
        let expr_node = expression expr in
        (pattern_nodes, expr_node) :: rest_node
    | _ -> failwith "Not a multiple matching"
  and let_binding (tree : (string, string) syntax_tree) : binding node =
    match tree with
    | Node ("LET_BINDING", [ pttrn; Leaf { token_type = "eq" }; expr ]) ->
        let pttrn_node = pattern pttrn in
        let expr_node = expression expr in
        Variable { lhs = pttrn_node; value = expr_node }
    | Node ("LET_BINDING", [ name; arguments; Leaf { token_type = "eq" }; expr ])
      ->
        let name_node = variable name in
        let argument_nodes = b_pattern_list arguments in
        let expr_node = expression expr in

        Function
          { name = name_node; parameters = argument_nodes; body = expr_node }
    | _ -> failwith "Not a let binding"
  and let_binding_list (tree : (string, string) syntax_tree) : binding node list
      =
    match tree with
    | Node ("LET_BINDING_LIST", [ b ]) -> [ let_binding b ]
    | Node ("LET_BINDING_LIST", [ b; Leaf { token_type = "and" }; rest ]) ->
        let_binding b :: let_binding_list rest
    | _ -> failwith "Not a binding list"
  and expression_sequence (tree : (string, string) syntax_tree) :
      expression node list =
    match tree with
    | Node
        ( "EXPR",
          [
            (Node ("EXPR", _) as e1);
            Leaf { token_type = "semicolon" };
            (Node ("EXPR", _) as e2);
          ] ) ->
        expression e1 :: expression_sequence e2
    | Node
        ("EXPR", [ (Node ("EXPR", _) as e1); Leaf { token_type = "semicolon" } ])
      ->
        [ expression e1 ]
    | _ -> [ expression tree ]
  and field_expression (tree : (string, string) syntax_tree) :
      label node * expression node =
    match tree with
    | Node ("FIELD_EXPR", [ name; Leaf { token_type = "eq" }; value ]) ->
        (label name, expression value)
    | _ -> failwith "Not a field expression"
  and field_expression_sequence (tree : (string, string) syntax_tree) :
      (label node * expression node) list =
    match tree with
    | Node ("FIELD_EXPR_LIST", [ expr ]) -> [ field_expression expr ]
    | Node ("FIELD_EXPR_LIST", [ expr; Leaf { token_type = "semicolon" } ]) ->
        [ field_expression expr ]
    | Node ("FIELD_EXPR_LIST", [ expr; Leaf { token_type = "semicolon" }; rest ])
      ->
        field_expression expr :: field_expression_sequence rest
    | _ -> failwith "Not a field expression list"
  and adjacent_expressions (tree : (string, string) syntax_tree) :
      expression node list =
    match tree with
    | Node ("EXPR", [ (Node ("EXPR", _) as e1); (Node ("EXPR", _) as e2) ]) ->
        adjacent_expressions e1 @ [ expression e2 ]
    | _ -> [ expression tree ]
  and expression_tuple (tree : (string, string) syntax_tree) :
      expression node list =
    match tree with
    | Node
        ( "EXPR",
          [
            (Node ("EXPR", _) as e1);
            Leaf { token_type = "comma" };
            (Node ("EXPR", _) as e2);
          ] ) ->
        expression_tuple e1 @ [ expression e2 ]
    | _ -> [ expression tree ]
  and expression (tree : (string, string) syntax_tree) : expression node =
    match tree with
    | Node ("EXPR", [ (Node ("VARIABLE", _) as var) ]) ->
        let var_node = variable var in
        Variable var_node
    | Node ("EXPR", [ (Node ("CONSTANT", _) as cst) ]) ->
        let cst_node = constant cst in
        Constant cst_node
    | Node
        ( "EXPR",
          [
            Leaf { token_type = "open_paren" };
            inner;
            Leaf { token_type = "close_paren" };
          ] ) ->
        let inner_node = expression inner in
        Parenthesised { style = Parenthesis; inner = inner_node }
    | Node
        ( "EXPR",
          [ Leaf { token_type = "begin" }; inner; Leaf { token_type = "end" } ]
        ) ->
        let inner_node = expression inner in
        Parenthesised { style = BeginEnd; inner = inner_node }
    | Node
        ( "EXPR",
          [
            Leaf { token_type = "open_paren" };
            inner;
            Leaf { token_type = "colon" };
            typ_expr;
            Leaf { token_type = "close_paren" };
          ] ) ->
        let inner_node = expression inner in
        let typ_expr_node = type_expression typ_expr in
        TypeCoercion { inner = inner_node; typ = typ_expr_node }
    | Node
        ( "EXPR",
          [
            Leaf { token_type = "open_bracket" };
            inner;
            Leaf { token_type = "close_bracket" };
          ] ) ->
        let inner_nodes = expression_sequence inner in
        ListLiteral inner_nodes
    | Node
        ( "EXPR",
          [
            Leaf { token_type = "open_bracket_bar" };
            inner;
            Leaf { token_type = "close_bracket_bar" };
          ] ) ->
        let inner_nodes = expression_sequence inner in
        ArrayLiteral inner_nodes
    | Node
        ( "EXPR",
          [
            Leaf { token_type = "open_brace" };
            inner;
            Leaf { token_type = "close_brace" };
          ] ) ->
        let inner_nodes = field_expression_sequence inner in
        RecordLiteral inner_nodes
    | Node
        ( "EXPR",
          [
            Leaf { token_type = "while" };
            condition;
            Leaf { token_type = "do" };
            body;
            Leaf { token_type = "done" };
          ] ) ->
        let condition_node = expression condition in
        let body_node = expression body in
        WhileLoop { body = body_node; condition = condition_node }
    | Node
        ( "EXPR",
          [
            Leaf { token_type = "for" };
            Leaf { value = var_name };
            Leaf { token_type = "eq" };
            start;
            Leaf { token_type = "to" };
            finish;
            Leaf { token_type = "do" };
            body;
            Leaf { token_type = "done" };
          ] ) ->
        let start_node = expression start in
        let finish_node = expression start in
        let body_node = expression body in

        ForLoop
          {
            direction = Up;
            body = body_node;
            start = start_node;
            finish = finish_node;
            variable = var_name;
          }
    | Node
        ( "EXPR",
          [
            Leaf { token_type = "for" };
            Leaf { value = var_name };
            Leaf { token_type = "eq" };
            start;
            Leaf { token_type = "downtn" };
            finish;
            Leaf { token_type = "do" };
            body;
            Leaf { token_type = "done" };
          ] ) ->
        let start_node = expression start in
        let finish_node = expression start in
        let body_node = expression body in

        ForLoop
          {
            direction = Down;
            body = body_node;
            start = start_node;
            finish = finish_node;
            variable = var_name;
          }
    | Node ("EXPR", [ Leaf { token_type = "bang" }; inner ]) ->
        let inner_node = expression inner in
        Dereference inner_node
    | Node ("EXPR", [ receiver; Leaf { token_type = "dot" }; target ]) ->
        let receiver_node = expression receiver in
        let target_node = label target in
        FieldAccess { receiver = receiver_node; target = target_node }
    | Node
        ( "EXPR",
          [
            receiver;
            Leaf { token_type = "dot_paren" };
            target;
            Leaf { token_type = "close_paren" };
          ] ) ->
        let receiver_node = expression receiver in
        let target_node = expression target in
        ArrayAccess { receiver = receiver_node; target = target_node }
    | Node ("EXPR", [ Node ("EXPR", _); Node ("EXPR", _) ]) ->
        let chain = adjacent_expressions tree in
        let receiver = List.hd chain in
        let arguments = List.tl chain in
        FunctionApplication { receiver; arguments }
    | Node
        ( "EXPR",
          [ Leaf { token_type = ("minus" | "minus_dot") as operation }; inner ]
        ) ->
        let inner_node = expression inner in

        PrefixOperation
          {
            operation =
              (match operation with
              | "minus" -> Minus
              | "minus_dot" -> MinusDot
              | _ -> failwith ("Unmatched operation: " ^ operation));
            receiver = inner_node;
          }
    | Node
        ( "EXPR",
          [
            lhs;
            Leaf
              {
                token_type =
                  ( "double_star" | "mod" | "star" | "star_dot" | "slash"
                  | "slash_dot" | "plus" | "plus_dot" | "minus" | "minus_dot"
                  | "double_colon" | "at" | "caret" | "eq" | "neq" | "double_eq"
                  | "bang_equals" | "less" | "leq" | "greater" | "geq"
                  | "less_dot" | "leq_dot" | "greater_dot" | "geq_dot"
                  | "ampersand" | "or" | "double_ampersand" | "double_pipe" ) as
                  operation;
              };
            rhs;
          ] ) ->
        let lhs_node = expression lhs in
        let rhs_node = expression rhs in
        InfixOperation
          {
            operation =
              (match operation with
              | "double_star" -> DoubleStar
              | "mod" -> Mod
              | "star" -> Star
              | "star_dot" -> StarDot
              | "slash" -> Slash
              | "slash_dot" -> SlashDot
              | "plus" -> Plus
              | "plus_dot" -> PlusDot
              | "minus" -> Minus
              | "minus_dot" -> MinusDot
              | "double_colon" -> DoubleColon
              | "at" -> At
              | "caret" -> Caret
              | "eq" -> Eq
              | "neq" -> Neq
              | "double_eq" -> DoubleEq
              | "bang_equals" -> BangEq
              | "less" -> Less
              | "leq" -> Leq
              | "greater" -> Greater
              | "geq" -> Geq
              | "less_dot" -> LessDot
              | "leq_dot" -> LeqDot
              | "greater_dot" -> GreaterDot
              | "geq_dot" -> GeqDot
              | "ampersand" -> Ampersand
              | "or" -> Or
              | "double_ampersand" -> DoubleAmpersand
              | "double_pipe" -> DoublePipe
              | _ -> failwith ("Unmatched operation: " ^ operation));
            lhs = lhs_node;
            rhs = rhs_node;
          }
    | Node ("EXPR", [ Leaf { token_type = "not" }; inner ]) ->
        let inner_node = expression inner in
        Negation inner_node
    | Node ("EXPR", [ _; Leaf { token_type = "comma" }; _ ]) ->
        let expressions = expression_tuple tree in
        Tuple expressions
    | Node
        ( "EXPR",
          [
            receiver;
            Leaf { token_type = "dot" };
            target;
            Leaf { token_type = "left_arrow" };
            value;
          ] ) ->
        let receiver_node = expression receiver in
        let target_node = label target in
        let value_node = expression value in

        FieldAssignment
          { value = value_node; target = target_node; receiver = receiver_node }
    | Node
        ( "EXPR",
          [
            receiver;
            Leaf { token_type = "dot_paren" };
            target;
            Leaf { token_type = "close_paren" };
            Leaf { token_type = "left_arrow" };
            value;
          ] ) ->
        let receiver_node = expression receiver in
        let target_node = expression target in
        let value_node = expression value in

        ArrayAssignment
          { value = value_node; target = target_node; receiver = receiver_node }
    | Node ("EXPR", [ receiver; Leaf { token_type = "colon_equals" }; value ])
      ->
        let receiver_node = expression receiver in
        let value_node = expression value in

        ReferenceAssignment { receiver = receiver_node; value = value_node }
    | Node
        ( "EXPR",
          [
            Leaf { token_type = "if" };
            condition;
            Leaf { token_type = "then" };
            body;
          ] ) ->
        let condition_node = expression condition in
        let body_node = expression body in

        If { else_body = None; body = body_node; condition = condition_node }
    | Node
        ( "EXPR",
          [
            Leaf { token_type = "if" };
            condition;
            Leaf { token_type = "then" };
            body;
            Leaf { token_type = "else" };
            else_body;
          ] ) ->
        let condition_node = expression condition in
        let body_node = expression body in
        let else_body_node = expression else_body in

        If
          {
            else_body = Some else_body_node;
            body = body_node;
            condition = condition_node;
          }
    | Node ("EXPR", [ _; Leaf { token_type = "semicolon" }; _ ]) ->
        let sequence = expression_sequence tree in
        Sequence sequence
    | Node
        ( "EXPR",
          [
            Leaf { token_type = "let" };
            bindings;
            Leaf { token_type = "in" };
            inner;
          ] ) ->
        let inner_node = expression inner in
        let bindings_nodes = let_binding_list bindings in

        LetBinding
          { is_rec = false; inner = inner_node; bindings = bindings_nodes }
    | Node
        ( "EXPR",
          [
            Leaf { token_type = "let" };
            Leaf { token_type = "rec" };
            bindings;
            Leaf { token_type = "in" };
            inner;
          ] ) ->
        let inner_node = expression inner in
        let bindings_nodes = let_binding_list bindings in

        LetBinding
          { is_rec = true; inner = inner_node; bindings = bindings_nodes }
    | Node
        ( "EXPR",
          [
            Leaf { token_type = "match" };
            value;
            Leaf { token_type = "with" };
            pattern_cases;
          ] ) ->
        let value_node = expression value in
        let pattern_case_nodes = simple_matching pattern_cases in
        Match { value = value_node; cases = pattern_case_nodes }
    | Node
        ( "EXPR",
          [
            Leaf { token_type = "try" };
            value;
            Leaf { token_type = "with" };
            pattern_cases;
          ] ) ->
        let value_node = expression value in
        let pattern_case_nodes = simple_matching pattern_cases in
        Try { value = value_node; cases = pattern_case_nodes }
    | Node ("EXPR", [ Leaf { token_type = "fun" }; pattern_cases ]) ->
        let pattern_case_nodes = multiple_matching pattern_cases in
        FunctionLiteral { style = Fun; cases = pattern_case_nodes }
    | Node ("EXPR", [ Leaf { token_type = "function" }; pattern_cases ]) ->
        let pattern_case_nodes = multiple_matching pattern_cases in

        FunctionLiteral { style = Function; cases = pattern_case_nodes }
    | Node
        ( "EXPR",
          [
            receiver;
            Leaf { token_type = "dot_open_bracket" };
            target;
            Leaf { token_type = "close_bracket" };
          ] ) ->
        let receiver_node = expression receiver in
        let target_node = expression target in

        StringAccess { receiver = receiver_node; target = target_node }
    | Node
        ( "EXPR",
          [
            receiver;
            Leaf { token_type = "dot_open_bracket" };
            target;
            Leaf { token_type = "close_bracket" };
            Leaf { token_type = "left_arrow" };
            value;
          ] ) ->
        let receiver_node = expression receiver in
        let target_node = expression target in
        let value_node = expression value in

        StringAssignment
          { value = value_node; target = target_node; receiver = receiver_node }
    | Node ("EXPR", [ _; Leaf { token_type = "semicolon" } ]) ->
        let sequence = expression_sequence tree in
        Sequence sequence
    | Node
        ( "EXPR",
          [
            Leaf { token_type = "match" };
            value;
            Leaf { token_type = "with" };
            Leaf { token_type = "pipe" };
            pattern_cases;
          ] ) ->
        let value_node = expression value in
        let pattern_case_nodes = simple_matching pattern_cases in
        Match { value = value_node; cases = pattern_case_nodes }
    | Node
        ( "EXPR",
          [
            Leaf { token_type = "try" };
            value;
            Leaf { token_type = "with" };
            Leaf { token_type = "pipe" };
            pattern_cases;
          ] ) ->
        let value_node = expression value in
        let pattern_case_nodes = simple_matching pattern_cases in
        Try { value = value_node; cases = pattern_case_nodes }
    | Node
        ( "EXPR",
          [
            Leaf { token_type = "fun" };
            Leaf { token_type = "pipe" };
            pattern_cases;
          ] ) ->
        let pattern_case_nodes = multiple_matching pattern_cases in
        FunctionLiteral { style = Fun; cases = pattern_case_nodes }
    | Node
        ( "EXPR",
          [
            Leaf { token_type = "function" };
            Leaf { token_type = "pipe" };
            pattern_cases;
          ] ) ->
        let pattern_case_nodes = multiple_matching pattern_cases in

        FunctionLiteral { style = Function; cases = pattern_case_nodes }
    | _ -> failwith "Not an expression"
  and value_definition (tree : (string, string) syntax_tree) :
      value_definition node =
    match tree with
    | Node ("VALUE_DEFINITION", [ Leaf { token_type = "let" }; bindings ]) ->
        let binding_nodes = let_binding_list bindings in
        { bindings = binding_nodes; is_rec = false }
    | Node
        ( "VALUE_DEFINITION",
          [ Leaf { token_type = "let" }; Leaf { token_type = "rec" }; bindings ]
        ) ->
        let binding_nodes = let_binding_list bindings in
        { bindings = binding_nodes; is_rec = true }
    | _ -> failwith "Not a value definition"
  and constructor_declaration (tree : (string, string) syntax_tree) :
      type_constructor_declaration node =
    match tree with
    | Node ("CONSTR_DECL", [ Leaf { token_type = "uppercase_ident"; value } ])
      ->
        { name = value; parameter = None }
    | Node
        ( "CONSTR_DECL",
          [
            Leaf { token_type = "uppercase_ident"; value };
            Leaf { token_type = "of" };
            argument;
          ] ) ->
        let argument_node = type_expression argument in
        { name = value; parameter = Some argument_node }
    | _ -> failwith "Not a type constructor declaration"
  and type_constructor_declaration_list (tree : (string, string) syntax_tree) :
      type_constructor_declaration node list =
    match tree with
    | Node ("TYPE_CONSTR_DECL_LIST", [ decl ]) ->
        [ constructor_declaration decl ]
    | Node
        ("TYPE_CONSTR_DECL_LIST", [ decl; Leaf { token_type = "pipe" }; rest ])
      ->
        constructor_declaration decl :: type_constructor_declaration_list rest
    | _ -> failwith "Not a type constructor declaration list"
  and label_declaration (tree : (string, string) syntax_tree) :
      field_declaration node =
    match tree with
    | Node
        ( "LABEL_DECL",
          [
            Leaf { token_type = "lowercase_ident"; value };
            Leaf { token_type = "colon" };
            typ_expr;
          ] ) ->
        let typ_expr_node = type_expression typ_expr in

        { name = value; typ = typ_expr_node; is_mutable = false }
    | Node
        ( "LABEL_DECL",
          [
            Leaf { token_type = "mutable" };
            Leaf { token_type = "lowercase_ident"; value };
            Leaf { token_type = "colon" };
            typ_expr;
          ] ) ->
        let typ_expr_node = type_expression typ_expr in

        { name = value; typ = typ_expr_node; is_mutable = true }
    | _ -> failwith "Not a label declaration"
  and label_declaration_list (tree : (string, string) syntax_tree) :
      field_declaration node list =
    match tree with
    | Node ("LABEL_DECL_LIST", [ decl ]) -> [ label_declaration decl ]
    | Node ("LABEL_DECL_LIST", [ decl; Leaf { token_type = "semicolon" }; rest ])
      ->
        label_declaration decl :: label_declaration_list rest
    | _ -> failwith "Not a label declaration"
  and type_parameter_list (tree : (string, string) syntax_tree) :
      lowercase_ident node list =
    match tree with
    | Node
        ( "TYPE_PARAM_LIST",
          [
            Leaf { token_type = "apostrophe" };
            Leaf { token_type = "lowercase_ident"; value };
          ] ) ->
        [ value ]
    | Node
        ( "TYPE_PARAM_LIST",
          [
            Leaf { token_type = "apostrophe" };
            Leaf { token_type = "lowercase_ident"; value };
            Leaf { token_type = "comma" };
            rest;
          ] ) ->
        value :: type_parameter_list rest
    | _ -> failwith "Not a type parameter list"
  and type_parameters (tree : (string, string) syntax_tree) :
      lowercase_ident node list * bool =
    match tree with
    | Node
        ( "TYPE_PARAMS",
          [
            Leaf { token_type = "apostrophe" };
            Leaf { token_type = "lowercase_ident"; value };
          ] ) ->
        ([ value ], false)
    | Node
        ( "TYPE_PARAMS",
          [
            Leaf { token_type = "open_paren" };
            list;
            Leaf { token_type = "close_paren" };
          ] ) ->
        (type_parameter_list list, true)
    | _ -> failwith "Not a type parameter list"
  and typedef (tree : (string, string) syntax_tree) : typedef node =
    match tree with
    | Node
        ( "TYPEDEF",
          [
            Leaf { token_type = "lowercase_ident"; value };
            Leaf { token_type = "eq" };
            (Node ("TYPE_CONSTR_DECL_LIST", _) as constructor_declarations);
          ] ) ->
        let constructor_declaration_nodes =
          type_constructor_declaration_list constructor_declarations
        in

        Constructors
          {
            name = value;
            parameters = [];
            parenthesised_parameters = false;
            constructors = constructor_declaration_nodes;
          }
    | Node
        ( "TYPEDEF",
          [
            Leaf { token_type = "lowercase_ident"; value };
            Leaf { token_type = "eq" };
            Leaf { token_type = "open_brace" };
            label_decl_list;
            Leaf { token_type = "close_brace" };
          ] ) ->
        Record
          {
            name = value;
            parameters = [];
            parenthesised_parameters = false;
            fields = label_declaration_list label_decl_list;
          }
    | Node
        ( "TYPEDEF",
          [
            Leaf { token_type = "lowercase_ident"; value };
            Leaf { token_type = "double_eq" };
            typ_expr;
          ] ) ->
        Alias
          {
            name = value;
            parameters = [];
            parenthesised_parameters = false;
            style = DoubleEq;
            aliased = type_expression typ_expr;
          }
    | Node ("TYPEDEF", [ Leaf { token_type = "lowercase_ident"; value } ]) ->
        Anonymous
          { name = value; parameters = []; parenthesised_parameters = false }
    | Node
        ( "TYPEDEF",
          [
            parameters;
            Leaf { token_type = "lowercase_ident"; value };
            Leaf { token_type = "eq" };
            (Node ("TYPE_CONSTR_DECL_LIST", _) as constructor_declarations);
          ] ) ->
        let parameters, parenthesised_parameters = type_parameters parameters in
        let constructor_declaration_nodes =
          type_constructor_declaration_list constructor_declarations
        in

        Constructors
          {
            name = value;
            parameters;
            parenthesised_parameters;
            constructors = constructor_declaration_nodes;
          }
    | Node
        ( "TYPEDEF",
          [
            parameters;
            Leaf { token_type = "lowercase_ident"; value };
            Leaf { token_type = "eq" };
            Leaf { token_type = "open_brace" };
            label_decl_list;
            Leaf { token_type = "close_brace" };
          ] ) ->
        let parameters, parenthesised_parameters = type_parameters parameters in

        Record
          {
            name = value;
            parameters;
            parenthesised_parameters;
            fields = label_declaration_list label_decl_list;
          }
    | Node
        ( "TYPEDEF",
          [
            parameters;
            Leaf { token_type = "lowercase_ident"; value };
            Leaf { token_type = "double_eq" };
            typ_expr;
          ] ) ->
        let parameters, parenthesised_parameters = type_parameters parameters in

        Alias
          {
            name = value;
            parameters;
            parenthesised_parameters;
            style = DoubleEq;
            aliased = type_expression typ_expr;
          }
    | Node
        ( "TYPEDEF",
          [ parameters; Leaf { token_type = "lowercase_ident"; value } ] ) ->
        let parameters, parenthesised_parameters = type_parameters parameters in

        Anonymous { name = value; parameters; parenthesised_parameters }
    | Node
        ( "TYPEDEF",
          [
            Leaf { token_type = "lowercase_ident"; value };
            Leaf { token_type = "eq" };
            typ_expr;
          ] ) ->
        Alias
          {
            name = value;
            parameters = [];
            parenthesised_parameters = false;
            style = SingleEq;
            aliased = type_expression typ_expr;
          }
    | Node
        ( "TYPEDEF",
          [
            parameters;
            Leaf { token_type = "lowercase_ident"; value };
            Leaf { token_type = "eq" };
            typ_expr;
          ] ) ->
        let parameters, parenthesised_parameters = type_parameters parameters in

        Alias
          {
            name = value;
            parameters;
            parenthesised_parameters;
            style = SingleEq;
            aliased = type_expression typ_expr;
          }
    | _ -> failwith "Not a typedef"
  and typedef_list (tree : (string, string) syntax_tree) : typedef node list =
    match tree with
    | Node ("TYPEDEF_LIST", [ typdef ]) -> [ typedef typdef ]
    | Node ("TYPEDEF_LIST", [ typdef; Leaf { token_type = "and" }; rest ]) ->
        typedef typdef :: typedef_list rest
    | _ -> failwith "Not a typedef list"
  and type_definition (tree : (string, string) syntax_tree) :
      type_definition node =
    match tree with
    | Node ("TYPE_DEFINITION", [ Leaf { token_type = "type" }; typdef_list ]) ->
        typedef_list typdef_list
    | _ -> failwith "Not a type definition"
  and exception_constructor_declaration_list
      (tree : (string, string) syntax_tree) :
      type_constructor_declaration node list =
    match tree with
    | Node ("EXCEPTION_CONSTR_DECL_LIST", [ decl ]) ->
        [ constructor_declaration decl ]
    | Node
        ( "EXCEPTION_CONSTR_DECL_LIST",
          [ decl; Leaf { token_type = "and" }; rest ] ) ->
        constructor_declaration decl
        :: exception_constructor_declaration_list rest
    | _ -> failwith "Not a type constructor declaration list"
  and exception_definition (tree : (string, string) syntax_tree) :
      exception_definition node =
    match tree with
    | Node ("EXCEPTION_DEFINITION", [ Leaf { token_type = "exception" }; list ])
      ->
        let list_node_s = exception_constructor_declaration_list list in
        { exceptions = list_node_s }
    | _ -> failwith "Not an exception definition"
  in

  let implementation_phrase (tree : (string, string) syntax_tree) : phrase node
      =
    match tree with
    | Node ("IMPL_PHRASE", [ (Node ("EXPR", _) as expr) ]) ->
        let expr_node = expression expr in
        Expression expr_node
    | Node ("IMPL_PHRASE", [ (Node ("VALUE_DEFINITION", _) as val_def) ]) ->
        let val_def_node = value_definition val_def in
        ValueDefinition val_def_node
    | Node ("IMPL_PHRASE", [ (Node ("TYPE_DEFINITION", _) as typ_def) ]) ->
        let typ_def_node = type_definition typ_def in
        TypeDefinition typ_def_node
    | Node ("IMPL_PHRASE", [ (Node ("EXCEPTION_DEFINITION", _) as exc_def) ]) ->
        let exc_def_node = exception_definition exc_def in
        ExceptionDefinition exc_def_node
    | _ -> failwith "Not an implementation phrase"
  in

  match tree with
  | Node ("IMPLEMENTATION", [ phrase; Leaf { token_type = "double_semicolon" } ])
    ->
      let phrase_node = implementation_phrase phrase in
      [ phrase_node ]
  | Node ("IMPLEMENTATION", [ phrase ]) ->
      let phrase_node = implementation_phrase phrase in
      [ phrase_node ]
  | Node
      ( "IMPLEMENTATION",
        [ phrase; Leaf { token_type = "double_semicolon" }; remaining ] )
  | Node ("IMPLEMENTATION", [ phrase; remaining ]) ->
      let phrase_node = implementation_phrase phrase in
      let remaining_node = ast_of_syntax_tree remaining in
      phrase_node :: remaining_node
  | _ -> failwith "Not an implementation"

(** Converts a Caml Light AST back into Caml Light source. sink is called with
    string fragments which, when concatenated in the order they are passed to
    sink, form the program source. *)
let stringify_ast_into (ast : program) (sink : string -> unit) : unit =
  (* Required so OCaml does not instantiate 'a. *)
  let rec iter_with_join : 'a. ('a -> unit) -> string -> 'a list -> unit =
   fun f s l ->
    match l with
    | [] -> ()
    | x :: [] -> f x
    | x :: q ->
        f x;
        sink s;
        iter_with_join f s q
  in

  let rec handle_type_expression (e : type_expression) =
    match e with
    | Argument n ->
        sink "'";
        sink n
    | Parenthesised e ->
        sink "(";
        handle_type_expression e;
        sink ")"
    | Construction c ->
        (match c.arguments with
        | [] -> ()
        | [ e ] -> handle_type_expression e
        | _ ->
            sink "(";
            iter_with_join handle_type_expression ", " c.arguments;
            sink ")");
        sink " ";
        sink c.constructor
    | Tuple t -> iter_with_join handle_type_expression " * " t
    | Function f ->
        handle_type_expression f.argument;
        sink " -> ";
        handle_type_expression f.result
  in

  let handle_constructor (c : constructor) =
    match c with
    | Named n -> sink n
    | EmptyList -> sink "[]"
    | Unit style -> sink (if style = Parenthesis then "()" else "begin end")
    | EmptyArray -> sink "[||]"
  in

  let handle_constant (c : constant) =
    match c with
    | IntegerLiteral i -> sink (string_of_int i)
    | FloatLiteral f -> sink (string_of_float f)
    | CharacterLiteral c ->
        sink (if c.style = New then "'" else "`");
        sink (string_of_char c.value);
        sink (if c.style = New then "'" else "`")
    | StringLiteral s ->
        sink "\"";
        sink s;
        sink "\""
    | Construction c -> handle_constructor c
  in

  let rec handle_pattern (p : pattern) =
    match p with
    | Ident e -> sink e
    | Underscore -> sink "_"
    | Parenthesised p ->
        sink "(";
        handle_pattern p;
        sink ")"
    | TypeCoercion c ->
        sink "(";
        handle_pattern c.inner;
        sink " : ";
        handle_type_expression c.typ;
        sink ")"
    | Constant c -> handle_constant c
    | Record r ->
        sink "{";
        iter_with_join
          (fun (field, pattern) ->
            sink field;
            sink " = ";
            handle_pattern pattern)
          "; " r;
        sink "}"
    | List l ->
        sink "[";
        iter_with_join handle_pattern "; " l;
        sink "]"
    | Construction c ->
        handle_constructor c.constructor;
        sink " ";
        handle_pattern c.argument
    | Concatenation c ->
        handle_pattern c.head;
        sink " :: ";
        handle_pattern c.tail
    | Tuple t -> iter_with_join handle_pattern ", " t
    | Or o -> iter_with_join handle_pattern " | " o
    | As a ->
        handle_pattern a.inner;
        sink " as ";
        sink a.name
  in

  let rec handle_binding (b : binding) =
    match b with
    | Variable v ->
        handle_pattern v.lhs;
        sink " = ";
        handle_expression v.value
    | Function f ->
        sink f.name;
        sink " ";
        iter_with_join handle_pattern " " f.parameters;
        sink " = ";
        handle_expression f.body
  and handle_expression (e : expression) =
    match e with
    | Variable v -> sink v
    | Constant c -> handle_constant c
    | Parenthesised e ->
        sink (if e.style = Parenthesis then "(" else "begin");
        handle_expression e.inner;
        sink (if e.style = Parenthesis then ")" else "end")
    | TypeCoercion e ->
        sink "(";
        handle_expression e.inner;
        sink " : ";
        handle_type_expression e.typ;
        sink ")"
    | ListLiteral l ->
        sink "[";
        iter_with_join handle_expression ";" l;
        sink "]"
    | ArrayLiteral l ->
        sink "[|";
        iter_with_join handle_expression ";" l;
        sink "|]"
    | RecordLiteral l ->
        sink "{";
        iter_with_join
          (fun (l, e) ->
            sink l;
            sink " = ";
            handle_expression e)
          ";" l;
        sink "}"
    | WhileLoop l ->
        sink "while ";
        handle_expression l.condition;
        sink " do ";
        handle_expression l.body;
        sink " done"
    | ForLoop l ->
        sink "for ";
        sink l.variable;
        sink " = ";
        handle_expression l.start;
        sink (if l.direction = Up then " to " else " downto ");
        handle_expression l.finish;
        sink " do ";
        handle_expression l.body;
        sink " done"
    | Dereference e ->
        sink "!";
        handle_expression e
    | FieldAccess a ->
        handle_expression a.receiver;
        sink ".";
        sink a.target
    | ArrayAccess a ->
        handle_expression a.receiver;
        sink ".(";
        handle_expression a.target;
        sink ")"
    | FunctionApplication f ->
        handle_expression f.receiver;
        sink " ";
        iter_with_join handle_expression " " f.arguments
    | PrefixOperation o ->
        sink (match o.operation with Minus -> "-" | MinusDot -> "-.");
        handle_expression o.receiver
    | InfixOperation o ->
        handle_expression o.lhs;
        sink
          (match o.operation with
          | DoubleStar -> " ** "
          | Mod -> " mod "
          | Star -> " * "
          | StarDot -> " *. "
          | Slash -> " / "
          | SlashDot -> " /. "
          | Plus -> " + "
          | PlusDot -> " +. "
          | Minus -> " - "
          | MinusDot -> " -. "
          | DoubleColon -> " :: "
          | At -> " @ "
          | Caret -> " ^ "
          | Eq -> " = "
          | Neq -> " <> "
          | DoubleEq -> " == "
          | BangEq -> " != "
          | Less -> " < "
          | Leq -> " <= "
          | Greater -> " > "
          | Geq -> " >= "
          | LessDot -> " <. "
          | LeqDot -> " <=. "
          | GreaterDot -> " >. "
          | GeqDot -> " >=. "
          | Ampersand -> " & "
          | Or -> " or "
          | DoubleAmpersand -> " && "
          | DoublePipe -> " || ");
        handle_expression o.rhs
    | Negation n ->
        sink "not ";
        handle_expression n
    | Tuple t -> iter_with_join handle_expression ", " t
    | FieldAssignment a ->
        handle_expression a.receiver;
        sink ".";
        sink a.target;
        sink " <- ";
        handle_expression a.value
    | ArrayAssignment a ->
        handle_expression a.receiver;
        sink ".(";
        handle_expression a.target;
        sink ") <- ";
        handle_expression a.value
    | ReferenceAssignment a ->
        handle_expression a.receiver;
        sink " := ";
        handle_expression a.value
    | If i -> (
        sink "if ";
        handle_expression i.condition;
        sink " then ";
        handle_expression i.body;
        match i.else_body with
        | None -> ()
        | Some b ->
            sink " else ";
            handle_expression b)
    | Sequence s -> iter_with_join handle_expression "; " s
    | Match m ->
        sink "match ";
        handle_expression m.value;
        sink " with ";
        iter_with_join
          (function
            | [ case ], expr ->
                handle_pattern case;
                sink " -> ";
                handle_expression expr
            | _ -> failwith "More than one case in match")
          "|" m.cases
    | Try t ->
        sink "try ";
        handle_expression t.value;
        sink " with ";
        iter_with_join
          (function
            | [ case ], expr ->
                handle_pattern case;
                sink " -> ";
                handle_expression expr
            | _ -> failwith "More than one case in match")
          "|" t.cases
    | FunctionLiteral f ->
        sink (if f.style = Fun then "fun " else "function ");
        iter_with_join
          (fun (cases, expr) ->
            iter_with_join handle_pattern " " cases;
            sink " -> ";
            handle_expression expr)
          "|" f.cases
    | LetBinding l ->
        sink "let ";
        if l.is_rec then sink "rec ";
        iter_with_join handle_binding " and " l.bindings;
        sink " in ";
        handle_expression l.inner
    | StringAccess s ->
        handle_expression s.target;
        sink ".[";
        handle_expression s.target;
        sink "]"
    | StringAssignment a ->
        handle_expression a.target;
        sink ".[";
        handle_expression a.target;
        sink "] <- ";
        handle_expression a.value
  in

  let handle_value_definition (v : value_definition) =
    sink "let ";
    if v.is_rec then sink "rec ";
    iter_with_join handle_binding " and " v.bindings
  in

  let handle_type_parameters (parenthesised : bool) (p : lowercase_ident list) =
    if parenthesised then sink "(";
    iter_with_join sink ", " (List.map (fun n -> "'" ^ n) p);
    if parenthesised then sink ")";
    sink " "
  in

  let handle_constructor_declaration (c : type_constructor_declaration) =
    sink c.name;
    match c.parameter with
    | None -> ()
    | Some p ->
        sink " of ";
        handle_type_expression p
  in

  let handle_field_declaration (f : field_declaration) =
    if f.is_mutable then sink "mutable ";
    sink f.name;
    sink " : ";
    handle_type_expression f.typ
  in

  let handle_typedef (t : typedef) =
    match t with
    | Constructors c ->
        handle_type_parameters c.parenthesised_parameters c.parameters;
        sink c.name;
        sink " = ";
        iter_with_join handle_constructor_declaration " | " c.constructors
    | Record r ->
        handle_type_parameters r.parenthesised_parameters r.parameters;
        sink r.name;
        sink "{";
        iter_with_join handle_field_declaration "; " r.fields;
        sink "}"
    | Alias a ->
        handle_type_parameters a.parenthesised_parameters a.parameters;
        sink a.name;
        sink (if a.style = SingleEq then " = " else " == ");
        handle_type_expression a.aliased
    | Anonymous a ->
        handle_type_parameters a.parenthesised_parameters a.parameters;
        sink a.name
  in

  let handle_type_definition (t : type_definition) =
    sink "type ";
    iter_with_join handle_typedef " and " t
  in

  let handle_exception_definition (e : exception_definition) =
    sink "exception ";
    iter_with_join handle_constructor_declaration " and " e.exceptions
  in

  let handle_phrase (phrase : phrase) =
    (match phrase with
    | Expression e -> handle_expression e
    | ValueDefinition v -> handle_value_definition v
    | TypeDefinition t -> handle_type_definition t
    | ExceptionDefinition e -> handle_exception_definition e);
    sink ";;"
  in
  List.iter handle_phrase ast

(** Converts a Caml Light AST to Caml Light source code. *)
let string_of_ast (ast : program) =
  let chain = ref [] in
  stringify_ast_into ast (fun piece -> chain := piece :: !chain);
  String.concat "" (List.rev !chain)

(** Parses a Caml Light AST from Caml Light source code. *)
let parse_caml_light_ast (source : string) : program =
  ast_of_syntax_tree (parse_caml_light_syntax_tree source)
