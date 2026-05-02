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
        bindings : binding list;
        is_rec : bool;
        inner : expression;
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


let whilify_bindings (def : value_definition) : value_definition list =
  (* Renvoie les nouvelles value_definition, et le renommage appliqué aux
   * fonctions modifiées *)
  let whilify_bindings_after_rectification (def : value_definition)
      (info: recursive_call_info) :
      value_definition list * ((label * label) list)=
    if
      not def.is_rec
      || not info.all_recursive_functions_are_toplevel
      || not (is_length_1 info.recursively_defined_functions)
    then
      [ def ], []
    else begin
      match List.hd def.bindings with
      | Function { name; parameters; return_type; body } ->
         let new_name = name ^ "_whilified" in
         let body_while = fonction_vers_while new_name parameters
                          body info.rectifying_set
         in
         [
           {
             bindings = [
               Function {
                 name = new_name;
                 parameters;
                 body = body_while;
                 return_type;
               }
             ];
             is_rec = false
           };
         ], [(name, new_name)]
      | _ -> [ def ], []
    end
  in

  let rectify_then_whilify (def : value_definition) : rectify_result =
    match rectify_bindings def.bindings with
    | NewBindings (b, Some info) ->
      let update_bindings (def : value_definition)
          (substitutions : (label * label) list) :
          value_definition list * ((label * label) list) =
        match def with
        | {
            is_rec = false;
            bindings = [
              Function (
                {
                  body = FunctionApplication {
                    receiver = Variable callee;
                    arguments
                  }
                } as f
              )
            ]
          } ->
          (* C’est un intercepteur créé pendant la rectification : on le met à
           * jour pour appelé la fonction rectifiée-whilifiée *)
          (
            [{
              is_rec = false;
              bindings = [
                Function {
                  f with
                  body = FunctionApplication {
                    receiver = Variable (
                      List.assoc_opt callee substitutions
                      |> Option.value ~default:callee
                    );
                    arguments;
                  };
                }
              ];
            }],
            []
          )
        | _ -> whilify_bindings_after_rectification def info
      in

      NewBindings (
        List.fold_left (fun (defs, subs) next_def ->
          let next_defs, next_subs = update_bindings next_def subs in
          defs @ next_defs, subs @ next_subs
        ) ([], []) b
        |> fst,
        None
      )
    | autre -> autre
  in

  try_transform_bindings_deep def rectify_then_whilify


let whilify_program (program: phrase list) =
  let whilify_phrase (phrase: phrase) : phrase list =
    match phrase with
    | ValueDefinition v -> begin
        whilify_bindings v
        |> List.map (fun v -> ValueDefinition v)
    end
    | _ -> [phrase]
  in
  program |> List.map whilify_phrase |> List.concat


