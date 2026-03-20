open Utils
open Caml_light
open Rectify
open Rectify_helper

(* Renvoie l’AST de la fonction récursive terminale f une fois avoir été
 * transformée en boucle while (la sortie est toujours l’AST d’une fonction).
 * Les appels récursifs sont supposés être faits sur des noms de variables
 * uniquement (i.e. la fonction appelée ne doit pas être le résultat d’une
 * expression) et la liste de variables pouvant conduire à un appel récursif
 * sont listées dans `recursive_call_names`.
 *)
let fonction_vers_while
    (name: variable)
    (parameters: pattern list)
    (body: expression)
    (recursive_call_names: variable list) : expression =

  (* Renvoie une liste de définitions de refs correspondant aux arguments *)
  let rec parameter_list_to_ref_list (p: string list) (inner_expr: expression) :
      expression =
    match p with
    | [] ->
        (LetBinding ({
          bindings = [
            Variable {
              lhs = Ident "res_ref";
              value = FunctionApplication {
                receiver = Variable "ref";
                arguments = [Variable "None"]
              }
            }
          ];
          is_rec = false;
          inner = inner_expr
        }))
    | x::q ->
        parameter_list_to_ref_list q
        (LetBinding {
          bindings = [
            Variable {
              lhs = Ident (x^"_ref");
              value = FunctionApplication {
                receiver = Variable "ref";
                arguments = [Variable x]
              }
            }
          ];
          is_rec = false;
          inner = inner_expr
        })
  in

  (* res_ref := Some(inner) *)
  let modify_res (inner: expression) : expression =
    ReferenceAssignment {
      receiver = Variable "res_ref";
      value =
        Parenthesised {
          style = Parenthesis;
          inner = FunctionApplication {
            receiver = Variable "Some";
            arguments = [Parenthesised{style=Parenthesis; inner}]
          }
        }
    }
  in

  (* Renvoie une liste de définitions de variables temporaires correspondant aux
   * anciennes valeurs des arguments *)
  let rec parameter_list_to_let_list (p: string list) (inner_expr: expression) :
      expression =
    match p with
    | [] -> inner_expr
    | x::q ->
        parameter_list_to_let_list q
        (LetBinding {
          bindings = [
            Variable {
              lhs = Ident x;
              value = Dereference(Variable(x^"_ref"))
            }
          ];
          is_rec = false;
          inner = inner_expr
        })
  in

  (* modifie `res_ref` quand on trouve la valeur de l’expression *)
  let rec replace_result (p: string list) (inner_expr: expression) :
      expression =
    match inner_expr with
    | Parenthesised { inner ; style } ->
        Parenthesised {
          inner = replace_result p inner ;
          style = style
        }
    | TypeCoercion {inner ; typ } ->
        TypeCoercion {
          inner = replace_result p inner ;
          typ = typ
        }
    | FunctionApplication { receiver ; arguments } ->
        begin match receiver with
        | Parenthesised { inner=Variable(rec_call_name) ; style=_ }
        | Variable(rec_call_name)
            when List.mem rec_call_name recursive_call_names ->
          let seq = Caml_light.Sequence (
            List.map
            (fun (nom, valeur) ->
              Caml_light.ReferenceAssignment {
                receiver = Variable(nom^"_ref");
                value = valeur
              }
            )
            (List.combine p arguments)
          )
          in
          Parenthesised {
            style = BeginEnd;
            inner = seq
          }
        | _ ->
          modify_res (FunctionApplication { receiver ; arguments })
        end
    | If { condition ; body ; else_body } ->
        If {
          condition = condition ;
          body = replace_result p body ;
          else_body =
            Option.map (replace_result p) else_body
        }
    | Sequence(l) ->
        let n = List.length l in
        Sequence (
          List.mapi (fun i x -> if i = (n-1) then replace_result p x else x) l
        )
    | Match { value ; cases } ->
        Match {
          value ;
          cases = List.map
            (fun (pattern, expr) -> (pattern, replace_result p expr))
            cases
        }
    | Try { value ; cases } ->
        Try {
          value ;
          cases = List.map
            (fun (pattern, expr) -> (pattern, replace_result p expr))
            cases
        }
    | FunctionLiteral f ->
        modify_res (FunctionLiteral f)
    | LetBinding {
        bindings : binding node list;
        is_rec : bool;
        inner : expression node;
      } ->
        LetBinding {
          bindings = List.map
            (fun (b: binding) ->
              match b with
              | Variable v -> (Variable v: binding)
              | Function { name ; parameters ; body ; return_type } ->
                  (* TODO à repenser *)
                  Function {
                    name ;
                    parameters ;
                    body ;
                    return_type
                  }
            ) bindings ;
          is_rec ;
          inner = replace_result p inner
        }
    | v -> modify_res v
  in

  let wrap_in_while (body: expression) : expression =
    Sequence [
      WhileLoop {
        condition = InfixOperation {
          lhs = Dereference(Variable "res_ref");
          rhs = Variable "None";
          operation = Eq
        };
        body;
      };
      FunctionApplication {
        receiver = FieldAccess { receiver = Variable "Option"; target = "get"};
        arguments = [
          Parenthesised {
            style = Parenthesis;
            inner = Dereference(Variable "res_ref")
          }
        ]
      }
    ]
  in

  let params = List.filter_map
    (fun (x: pattern) -> match x with
      | (TypeCoercion {inner = Ident name; _})
      | Ident name -> Some name
      | _ -> None
    ) parameters in
  replace_result params body
  |> parameter_list_to_let_list params
  |> wrap_in_while
  |> parameter_list_to_ref_list params


let parse_file name =
  let input_channel = open_in name in
  let content = really_input_string input_channel
      (in_channel_length input_channel) in
  close_in input_channel;
  parse_caml_light_ast content


let whilify_bindings (bindings: binding list) (is_rec: bool) :
    (binding list * bool) list =
  let create_interceptor (name: string) (parameters: pattern list)
      (return_type: type_expression option) : binding =
    Function {
      name;
      return_type;
      parameters =
        List.mapi
        Caml_light.(fun i x ->
           match x with
           | Ident(v) -> Ident(v)
           | TypeCoercion { inner=Ident(v); typ } ->
               TypeCoercion { inner=Ident(v); typ }
           | _ -> Ident("arg"^(string_of_int i))
        )
        parameters;
      body = FunctionApplication {
        receiver = Variable(name^"_whilified");
        arguments = List.mapi
          Caml_light.(fun i x ->
            match x with
            | Ident(v) -> Variable(v)
            | TypeCoercion { inner=Ident(v); typ } -> Variable(v)
            | _ -> Variable("arg"^(string_of_int i))
          ) parameters
      }
    }
  in
  let whilify_bindings_after_rectification (bindings: binding list)
      (new_is_rec: bool) (clot: variable list) : (binding list * bool) list =
    if not new_is_rec || not (is_length_1 bindings) then
      [bindings, new_is_rec]
    else begin
      match List.hd bindings with
      | Function { name; parameters; return_type; body } ->
         let body_while = fonction_vers_while (name^"_whilified") parameters
                          body clot in
         [
           [Function {
             name = name^"_whilified";
             parameters;
             body = body_while;
             return_type;
           }], false;
           [create_interceptor name parameters return_type], false
         ]
      | autre -> [[autre], new_is_rec]
    end
  in

  let rectify_then_whilify (bindings: binding list) (is_rec': bool) :
      rectify_result =
    match rectify_bindings bindings with
    | NewBindings (b, clot) ->
      NewBindings (
        List.map (fun (new_bindings, is_rec'') ->
          whilify_bindings_after_rectification new_bindings is_rec'' clot
        ) b |> List.flatten, clot
      )
    | autre -> autre
  in

  try_transform_bindings_deep bindings is_rec rectify_then_whilify


let whilify_program (program: phrase list) =
  let whilify_phrase (phrase: phrase) : phrase list =
    match phrase with
    | ValueDefinition { bindings; is_rec } -> begin
        whilify_bindings bindings is_rec
        |> List.map (fun (new_binding, new_is_rec) ->
            ValueDefinition {
              bindings = new_binding;
              is_rec = new_is_rec;
            })
    end
    | _ -> [phrase]
  in
  program |> List.map whilify_phrase |> List.concat


