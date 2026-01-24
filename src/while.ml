open Caml_light
open Rectify

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

  (* Renvoie soit res_ref := Some(inner) soit (inner) en fonction de
   * `can_return` *)
  let modify_res (inner: expression) (can_return: bool): expression =
    if can_return then
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
    else
      inner
  in

  (* Renvoie une liste de définitions de variables temporaires correspondant aux
   * arguments *)
  let rec parameter_list_to_temp_list (p: string list)
      (new_vals: expression list) (inner_expr: expression) : expression =
    match p, new_vals with
    | [], [] -> inner_expr
    | [], _ | _, [] -> failwith "pas la même taille"
    | x::q, v::qv ->
        parameter_list_to_temp_list q qv
        (LetBinding {
          bindings = [
            Variable {
              lhs = Ident (x^"_temp");
              value = replace_args_with_refs p false v
            }
          ];
          is_rec = false;
          inner = inner_expr
        })

  (* Remplace les références aux arguments par les refs correspondants.
   * can_return indique si on doit modifier `res_ref` quand on trouve la valeur
   * de l’expression *)
  and replace_args_with_refs (p: string list) (can_return: bool)
      (inner_expr: expression) : expression =
    match inner_expr with
    | Variable(s) ->
        modify_res
          (if List.mem s p then
            Dereference(Variable(s^"_ref"))
          else
            Variable(s))
          can_return
    | Constant(c) -> modify_res (Constant(c)) can_return
    | Parenthesised { inner ; style } ->
        Parenthesised {
          inner = replace_args_with_refs p can_return inner ;
          style = style
        }
    | TypeCoercion {inner ; typ } ->
        TypeCoercion {
          inner = replace_args_with_refs p can_return inner ;
          typ = typ
        }
    | ListLiteral(l) ->
        modify_res
        (ListLiteral (List.map (replace_args_with_refs p false) l))
        can_return
    | ArrayLiteral(l) ->
        modify_res
        (ArrayLiteral (List.map (replace_args_with_refs p false) l))
        can_return
    | RecordLiteral(l) ->
        modify_res
        (RecordLiteral
          (List.map (
            fun (lbl, expr) -> (lbl, replace_args_with_refs p false expr)
          ) l))
        can_return
    | WhileLoop { condition ; body } ->
        modify_res
        (WhileLoop {
          condition = replace_args_with_refs p false condition ;
          body = replace_args_with_refs p false body
        })
        can_return
    | ForLoop { direction; variable; start; finish; body } ->
        modify_res
        (ForLoop {
          direction = direction;
          variable = variable;
          start = replace_args_with_refs p false start;
          finish = replace_args_with_refs p false finish;
          body = replace_args_with_refs p false body
        })
        can_return
    | Dereference(e) ->
        modify_res (Dereference(replace_args_with_refs p false e)) can_return
    | FieldAccess { receiver ; target } ->
        modify_res (FieldAccess {
          receiver = replace_args_with_refs p false receiver ;
          target
        }) can_return
    | ArrayAccess { receiver ; target } ->
        modify_res (ArrayAccess {
          receiver = replace_args_with_refs p false receiver ;
          target = replace_args_with_refs p false target
        }) can_return
    | FunctionApplication { receiver ; arguments } ->
        begin match receiver with
        | Parenthesised { inner=Variable(rec_call_name) ; style=_ }
        | Variable(rec_call_name)
            when List.mem rec_call_name recursive_call_names ->
          let seq = Caml_light.Sequence (
            List.map
            (fun nom ->
              Caml_light.ReferenceAssignment {
                receiver = Variable(nom^"_ref");
                value = Variable(nom^"_temp")
              }
            )
            p
          )
          in
          Parenthesised {
            style = BeginEnd;
            inner = parameter_list_to_temp_list p arguments seq
          }
        | _ ->
          modify_res (FunctionApplication {
            receiver = replace_args_with_refs p false receiver ;
            arguments = List.map (replace_args_with_refs p false) arguments
          }) can_return
        end
    | PrefixOperation { receiver ; operation } ->
        modify_res (PrefixOperation {
          receiver = replace_args_with_refs p false receiver ;
          operation
        }) can_return
    | InfixOperation { lhs ; rhs ; operation } ->
        modify_res (InfixOperation {
          lhs = replace_args_with_refs p false lhs ;
          rhs = replace_args_with_refs p false rhs ;
          operation
        }) can_return
    | Negation(e) ->
        modify_res (Negation(replace_args_with_refs p false e)) can_return
    | Tuple(l) ->
        modify_res (Tuple (List.map (replace_args_with_refs p false) l))
          can_return
    | FieldAssignment { receiver ; target ; value } ->
        modify_res
        (FieldAssignment {
          receiver = replace_args_with_refs p false receiver ;
          target;
          value = replace_args_with_refs p false value
        })
        can_return
    | ArrayAssignment { receiver ; target ; value } ->
        modify_res (ArrayAssignment {
          receiver = replace_args_with_refs p false receiver ;
          target = replace_args_with_refs p false target ;
          value = replace_args_with_refs p false value
        })
        can_return
    | ReferenceAssignment { receiver ; value } ->
        modify_res (ReferenceAssignment {
          receiver = replace_args_with_refs p false receiver ;
          value = replace_args_with_refs p false value
        }) can_return
    | If { condition ; body ; else_body } ->
        If {
          condition = replace_args_with_refs p false condition ;
          body = replace_args_with_refs p can_return body ;
          else_body =
            match else_body with
            | None -> None
            | Some(e) -> Some(replace_args_with_refs p can_return e)
        }
    | Sequence(l) ->
        let n = List.length l in
        Sequence (List.mapi (
          fun i x -> replace_args_with_refs p (can_return && i = (n-1)) x
        ) l)
    | Match { value ; cases } ->
        Match {
          value = replace_args_with_refs p false value ;
          cases = List.map
            (fun (pattern, expr) ->
              (pattern, replace_args_with_refs p can_return expr))
            cases
        }
    | Try { value ; cases } ->
        Try {
          value = replace_args_with_refs p false value ;
          cases = List.map
            (fun (pattern, expr) ->
              (pattern, replace_args_with_refs p can_return expr))
            cases
        }
    | FunctionLiteral { style ; cases } ->
        (* TODO à repenser certainement *)
        modify_res (FunctionLiteral {
          style;
          cases = List.map
            (fun (pattern, expr) ->
              (pattern, replace_args_with_refs p false expr))
            cases
        }) can_return
    | LetBinding {
        bindings : binding node list;
        is_rec : bool;
        inner : expression node;
      } ->
        LetBinding {
          bindings = List.map
            (fun (b: binding) ->
              match b with
              | Variable { lhs ; value } ->
                  (Variable {
                    lhs ;
                    value = replace_args_with_refs p false value
                  }: binding)
              | Function { name ; parameters ; body } ->
                  (* TODO à repenser aussi *)
                  Function {
                    name ;
                    parameters ;
                    body = replace_args_with_refs p false body
                  }
            ) bindings ;
          is_rec ;
          inner = replace_args_with_refs p can_return inner
        }
    | StringAccess { receiver ; target } ->
        modify_res (StringAccess {
          receiver = replace_args_with_refs p false receiver;
          target = replace_args_with_refs p false target
        }) can_return
    | StringAssignment { receiver ; target ; value } ->
        modify_res (StringAssignment {
          receiver = replace_args_with_refs p false receiver;
          target = replace_args_with_refs p false target;
          value = replace_args_with_refs p false value;
        }) can_return
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
  parameter_list_to_ref_list params
    (wrap_in_while (replace_args_with_refs params true body))


let parse_file name =
  let input_channel = open_in name in
  let content = really_input_string input_channel
      (in_channel_length input_channel) in
  close_in input_channel;
  parse_caml_light_ast content


let whilify (program: phrase list) =
  let interceptor (name: string) (parameters: pattern list) : binding =
    Function {
      name = name;
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
          ) parameters @ [
            Parenthesised {
              style = Parenthesis;
              inner = FunctionLiteral {
                style = Fun;
                cases = [[Ident "x"], Variable "x"]
              }
            }
          ]
      }
    }
  in
  let whilify_phrase (phrase: phrase) : phrase list =
    match phrase with
    | ValueDefinition { bindings; is_rec }
        when is_rec && List.length bindings = 1 -> (
      let one_binding = List.hd bindings in

      let linearised_binding_option =
        match one_binding with
        | Variable _ -> None
        | Function {name; parameters; body} ->
            let body_lin, _ = linearize body 0 in
            Some (
              name,
              FunctionLiteral {
                style = Fun;
                cases = [(parameters, body_lin)];
              }
            )
        in

        match linearised_binding_option with
        | None -> [phrase]
        | Some linearised_binding -> begin
          let new_name (n : string) = n ^ "_rectified" in

          match cloture_rectifiable [linearised_binding] with
          | None ->
              print_endline
               ("(* Avertissement : cloture_rectifiable a renvoyé None " ^
                "pour la fonction" ^ (fst linearised_binding) ^ " *)");
              [phrase]
          | Some clot ->
            let name, new_fn, parameters = match linearised_binding with
            | name, (
              FunctionLiteral {
                style; cases = [(parameters, body_lin)]
              }) ->
               let body_delin, _ =
                delinearize
                  (push_rectified_definitions
                     (rectify body_lin clot)
                     clot new_name) [] in
               let body_while =
                 fonction_vers_while
                   (new_name name) (parameters @ [Ident "cont"]) body_delin
                   (List.map new_name clot) in
               name, (Function {
                   name = name^"_whilified";
                   parameters = parameters @ [Ident "cont"];
                   body = body_while
                } : Caml_light.binding), parameters
            | _ -> failwith "Pas une fonction ?"

            in
            [
              ValueDefinition {
                is_rec = false;
                bindings = [new_fn]
              } ; ValueDefinition {
                is_rec = false;
                bindings = [interceptor name parameters]
              }
           ]
         end)
    | _ -> [phrase]
  in
  program |> List.map whilify_phrase |> List.concat


let main () =
  let test_source =
    if Array.length Sys.argv <= 1 then
      failwith "Merci de donner un argument : le nom de fichier"
    else begin
      let test_source_fp = open_in Sys.argv.(1) in
      let test_source =
        really_input_string test_source_fp (in_channel_length test_source_fp)
      in
      close_in test_source_fp;
      test_source
    end
  in
  let program = parse_caml_light_ast test_source in
  whilify program |> string_of_ast


let () = print_endline (main ())

